{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
module Data.Profunctor.Cocartesian.Free(
    -- * The free 'Cocartesian' profunctors
    FreeCocartesian(..),
    liftF, foldFree,
    emptyF, sumF, sumDayF,

    -- * Newtype wrapper
    ForgetCocartesian(..),
) where

import Data.Void (Void, absurd)
import Data.Profunctor (Profunctor(..), (:->))
import Data.Profunctor.Cartesian
import Data.Profunctor.Monad
import Data.Profunctor.Day

-- * Free Cocartesian

-- | @FreeCocartesian p@ is a 'Cartesian' profunctor freely generated from
--   a mere @Profunctor p@.
data FreeCocartesian p a b =
    Neutral (a -> Void)
  | Cons (Day Either p (FreeCocartesian p) a b)
  deriving Functor

instance Profunctor (FreeCocartesian p) where
    dimap f g fp = case fp of
        Neutral a -> Neutral (a . f)
        Cons ps' -> Cons (dimap f g ps')

instance ProfunctorFunctor FreeCocartesian where
  promap pq ps = case ps of
    Neutral a -> Neutral a
    Cons (Day p ps' opA opB) -> Cons $ Day (pq p) (promap pq ps') opA opB

emptyF :: FreeCocartesian p Void b
emptyF = Neutral id

sumDayF :: Day Either (FreeCocartesian p) (FreeCocartesian p) :-> FreeCocartesian p
sumDayF (Day (Neutral z) qs opA opB) = dimap (either (absurd . z) id . opA) (opB . Right) qs
sumDayF (Day (Cons ps) qs opA opB) = Cons $ promap2 sumDayF $ assocDay (Day ps qs opA opB)

sumF :: FreeCocartesian p a b -> FreeCocartesian p a' b' -> FreeCocartesian p (Either a a') (Either b b')
sumF ps qs = sumDayF (Day ps qs id id)

instance Profunctor p => Cocartesian (FreeCocartesian p) where
    proEmpty = emptyF
    proSum opA opB ps qs = sumDayF (Day ps qs opA opB)

-- * ProfunctorMonad structures

liftF :: p :-> FreeCocartesian p
liftF p = Cons $ Day p emptyF Left (either id absurd)

foldFree :: (Cocartesian q) => (p :-> q) -> FreeCocartesian p :-> q
foldFree handle ps = case ps of
    Neutral z -> lmap z proEmpty
    Cons (Day p ps' opA opB) -> dimap opA opB (handle p +++ foldFree handle ps')

instance ProfunctorMonad FreeCocartesian where
    proreturn = liftF
    projoin = foldFree id

-- * Utility newtype wrappers

-- | Forgets 'Cocartesian' instance from a 'Profunctor'.
newtype ForgetCocartesian p a b = ForgetCocartesian { recallCocartesian :: p a b }
  deriving newtype (Functor, Profunctor, Cartesian)
  -- DO NOT add "deriving Cocartesian" clause!
