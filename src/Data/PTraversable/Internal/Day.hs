{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions #-}

module Data.PTraversable.Internal.Day
  (ptraverseDay, ptraverseDayWith) where

import Prelude hiding (Enum)

import Data.Profunctor
import Data.Profunctor.Cartesian

import Data.Functor.Day ( Day(..), trans1, trans2 )

import Data.Finitary.PolyRep
import Data.Type.Equality

import Data.PTraversable.Internal.ClassOnly

-- * Auxiliary definitions

data EncoderF t where
  EncoderF :: !(SPoly r) -> (forall a. t a -> Eval r a) -> (forall b. Eval r b -> t b) -> EncoderF t

unsafeGeneralizeEncoder :: forall t. (forall a b. Encoder a b (t a) (t b)) -> EncoderF t
unsafeGeneralizeEncoder polyEncoder = case polyEncoder of
  Encoder sr _ _ -> EncoderF sr (from sr) (to sr)
  where
    from :: forall r a. SPoly r -> t a -> Eval r a 
    from sr = case polyEncoder of
      Encoder sr' from' _ -> case testEquality sr sr' of
        Nothing -> error "should not happen (parametricity)"
        Just Refl -> from'
    
    to :: forall r a. SPoly r -> Eval r a -> t a
    to sr = case polyEncoder of
      Encoder sr' _ to' -> case testEquality sr sr' of
        Nothing -> error "should not happen (parametricity)"
        Just Refl -> to'

dayEncoderF :: EncoderF t -> EncoderF u -> EncoderF (Day t u)
dayEncoderF @t @u (EncoderF @r1 sr1 fromT toT) (EncoderF @r2 sr2 fromU toU) =
  EncoderF (sDayPoly sr1 sr2) from to
  where
    from :: forall x. Day t u x -> Eval (DayPoly r1 r2) x
    from = fromDay sr1 sr2 . trans1 fromT . trans2 fromU 

    to :: forall x. Eval (DayPoly r1 r2) x -> Day t u x
    to = trans2 toU . trans1 toT . toDay sr1 sr2

-----------

-- | 'Day' lacks various instances required to be a 'PTraversable'
ptraverseDayWith :: forall t u.
     (PTraversable t, PTraversable u)
  => forall p a b as bs. (Cartesian p, Cocartesian p)
  => (as -> Day t u a) -> (Day t u b -> bs) -> p a b -> p as bs
ptraverseDayWith = travDayTU
  where
    encT :: EncoderF t
    encT = unsafeGeneralizeEncoder (ptraverse idEncoder)

    encU :: EncoderF u
    encU = unsafeGeneralizeEncoder (ptraverse idEncoder)

    encDayTU :: EncoderF (Day t u)
    encDayTU = dayEncoderF encT encU

    travDayTU :: forall p a b as bs. (Cartesian p, Cocartesian p)
      => (as -> Day t u a) -> (Day t u b -> bs) -> p a b -> p as bs
    travDayTU pre post = case encDayTU of
      EncoderF sr from to -> dimap (from . pre) (post . to) . ptraverseEval sr

ptraverseDay :: forall t u.
     (PTraversable t, PTraversable u)
  => forall p a b. (Cartesian p, Cocartesian p)
  => p a b -> p (Day t u a) (Day t u b)
ptraverseDay = ptraverseDayWith id id