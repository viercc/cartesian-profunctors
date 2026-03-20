{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE EmptyCase #-}
module Data.Finitary.TreeRep where

import Data.Kind (Type)

import Data.Bifunctor (Bifunctor(..))
import Data.Void (absurd)
import Data.Functor.Classes ( Eq1(..), Ord1(..), compare1, eq1 )

import Data.Profunctor (Profunctor (..))
import Data.Profunctor.Cartesian
    ( Cartesian(proUnit, (***)), Cocartesian(proEmpty, (+++)) )

-- | Representation of a finitary functor.
--
-- If we write @{r}@ to mean the type @r :: Rep@
-- represents,
--
-- > r = [t1, t2, ...]
--
-- represent sum type
--
-- > {t1} + {t2} + ...
type Rep = [TreeRep]

-- | Representation of a simple (= not a sum of multiple reps)
--   finitary functor.
--
-- - @UnitRep@ represents a unit type: @{UnitRep}(a) = ()@.
-- - @ParRep r@ represents a type with one parameter type prepended:
--   @{ParRep r}(a) = (a, {r}(a))@.
data TreeRep =
    UnitRep
  | ParRep Rep

addRep :: Rep -> Rep -> Rep
addRep = (++)

multRep :: Rep -> Rep -> Rep
multRep r1 r2 = concatMap (`multTreeRep` r2) r1

multTreeRep :: TreeRep -> Rep -> Rep
multTreeRep UnitRep r2 = r2
multTreeRep (ParRep s1) r2 = [ParRep $ multRep s1 r2]

-- | Representation of the identity functor
idRep :: Rep
idRep = [ParRep [UnitRep]]

-- | Representation of @Maybe@
maybeRep :: Rep
maybeRep = UnitRep : idRep

-----------------------------

-- * Type-level promoted Rep and its singleton reflection

type family AddRep (r1 :: Rep) (r2 :: Rep) :: Rep where
  AddRep '[] r2 = r2
  AddRep (t ': r1) r2 = t : AddRep r1 r2

type family MultRep (r1 :: Rep) (r2 :: Rep) :: Rep where
  MultRep '[] _ = '[]
  MultRep (UnitRep ': r1) r2 = AddRep r2 (MultRep r1 r2)
  MultRep (ParRep sub1 ': r1) r2 = ParRep (MultRep sub1 r2) ': MultRep r1 r2

data SRep (r :: Rep) where
  SEmpty :: SRep '[]
  SCase :: STreeRep t -> SRep r -> SRep (t ': r)

data STreeRep (t :: TreeRep) where
  SUnit :: STreeRep 'UnitRep
  SPar :: SRep r -> STreeRep ('ParRep r)

(%++) :: SRep r1 -> SRep r2 -> SRep (AddRep r1 r2)
SEmpty %++ sr2 = sr2
SCase st1 sr1 %++ sr2 = SCase st1 (sr1 %++ sr2)

(%*) :: SRep r1 -> SRep r2 -> SRep (MultRep r1 r2)
sr1 %* sr2 = case sr1 of
  SEmpty -> SEmpty
  SCase SUnit sr1' -> sr2 %++ (sr1' %* sr2)
  SCase (SPar ssub1) sr1' -> SCase (SPar (ssub1 %* sr2)) (sr1' %* sr2)

-----------------------------

-- * Interpreting @Rep@ as a real data type

data Eval (r :: Rep) (a :: Type) where
  EHere :: EvalT t a -> Eval (t ': r) a
  EThere :: Eval r a -> Eval (t ': r) a

data EvalT (t :: TreeRep) (a :: Type) where
  EUnit :: EvalT 'UnitRep a
  EPar :: a -> Eval r a -> EvalT ('ParRep r) a

-- Instances

deriving instance Functor (Eval r)
deriving instance Foldable (Eval r)
deriving instance Traversable (Eval r)

deriving instance Functor (EvalT t)
deriving instance Foldable (EvalT t)
deriving instance Traversable (EvalT t)

instance Eq a => Eq (Eval r a) where
  (==) = eq1

instance Eq1 (Eval r) where
  liftEq eq (EHere x) (EHere y) = liftEq eq x y
  liftEq eq (EThere x) (EThere y) = liftEq eq x y
  liftEq _ _ _ = False

instance Eq a => Eq (EvalT t a) where
  (==) = eq1

instance Eq1 (EvalT t) where
  liftEq _ EUnit EUnit = True
  liftEq eq (EPar a x) (EPar b y) = eq a b && liftEq eq x y

instance Ord a => Ord (Eval r a) where
  compare = compare1

instance Ord1 (Eval r) where
  liftCompare cmp (EHere x) (EHere y) = liftCompare cmp x y
  liftCompare _   (EHere _) (EThere _) = LT 
  liftCompare _   (EThere _) (EHere _) = GT
  liftCompare cmp (EThere x) (EThere y) = liftCompare cmp x y

instance Ord a => Ord (EvalT t a) where
  compare = compare1

instance Ord1 (EvalT t) where
  liftCompare _ EUnit EUnit = EQ
  liftCompare cmp (EPar a x) (EPar b y) = cmp a b <> liftCompare cmp x y

-- ** Add/Mult of @Rep@ corresponds to sum/product of Eval

absurdEval :: Eval '[] a -> any
absurdEval x = case x of {}

sumEval :: SRep r1 -> proxy r2 -> Either (Eval r1 x) (Eval r2 x) -> Eval (AddRep r1 r2) x
sumEval r1 r2 = either (inlEval r1 r2) (inrEval r1 r2)

inlEval :: SRep r1 -> proxy r2 -> Eval r1 x -> Eval (AddRep r1 r2) x
inlEval SEmpty _ x = absurdEval x
inlEval (SCase _ r1) r2 x = case x of
  EHere x' -> EHere x'
  EThere x' -> EThere (inlEval r1 r2 x')

inrEval :: SRep r1 -> proxy r2 -> Eval r2 x -> Eval (AddRep r1 r2) x
inrEval SEmpty _ y = y
inrEval (SCase _ r1) r2 y = EThere (inrEval r1 r2 y)

evalToSum :: SRep r1 -> proxy r2 -> Eval (AddRep r1 r2) x -> Either (Eval r1 x) (Eval r2 x)
evalToSum SEmpty _r2 z = Right z
evalToSum (SCase _ r1) r2 z = case z of
  EHere x -> Left (EHere x)
  EThere z' -> first EThere $ evalToSum r1 r2 z'

prodEval :: SRep r1 -> SRep r2 -> Eval r1 x -> Eval r2 x -> Eval (MultRep r1 r2) x
prodEval r1 r2 x y = case r1 of
  SEmpty -> absurdEval x
  SCase SUnit r1' -> case x of
    EHere EUnit -> inlEval r2 (r1' %* r2) y
    EThere x' -> inrEval r2 (r1' %* r2) (prodEval r1' r2 x' y)
  SCase (SPar sub1) r1' -> case x of
    EHere (EPar a x') -> EHere (EPar a (prodEval sub1 r2 x' y))
    EThere x' -> EThere (prodEval r1' r2 x' y)

evalToProd :: SRep r1 -> SRep r2 -> Eval (MultRep r1 r2) x -> (Eval r1 x, Eval r2 x)
evalToProd r1 r2 z = case r1 of
  SEmpty -> absurdEval z
  SCase SUnit r1' -> case evalToSum r2 (r1' %* r2) z of
    Left y -> (EHere EUnit, y)
    Right z' -> first EThere $ evalToProd r1' r2 z'
  SCase (SPar sub1) r1' -> case z of
    EHere (EPar a z') -> first (EHere . EPar a) $ evalToProd sub1 r2 z'
    EThere z' -> first EThere $ evalToProd r1' r2 z'

fstEval :: SRep r1 -> SRep r2 -> Eval (MultRep r1 r2) x -> Eval r1 x
fstEval r1 r2 z = case r1 of
  SEmpty -> absurdEval z
  SCase SUnit r1' -> case evalToSum r2 (r1' %* r2) z of
    Left _ -> EHere EUnit
    Right z' -> EThere $ fstEval r1' r2 z'
  SCase (SPar sub1) r1' -> case z of
    EHere (EPar a z') -> EHere . EPar a $ fstEval sub1 r2 z'
    EThere z' -> EThere $ fstEval r1' r2 z'

sndEval :: SRep r1 -> SRep r2 -> Eval (MultRep r1 r2) x -> Eval r2 x
sndEval r1 r2 z = case r1 of
  SEmpty -> absurdEval z
  SCase SUnit r1' -> case evalToSum r2 (r1' %* r2) z of
    Left y -> y
    Right z' -> sndEval r1' r2 z'
  SCase (SPar sub1) r1' -> case z of
    EHere (EPar _ z') -> sndEval sub1 r2 z'
    EThere z' -> sndEval r1' r2 z'

-- * Encoding / Decoding

data Encoder a b s t where
  Encoder :: SRep r -> (s -> Eval r a) -> (Eval r b -> t) -> Encoder a b s t

deriving instance Functor (Encoder a b s)

instance Profunctor (Encoder a b) where
  dimap f g (Encoder rep enc dec) = Encoder rep (enc . f) (g . dec)
  lmap f (Encoder rep enc dec) = Encoder rep (enc . f) dec
  rmap = fmap

instance Cartesian (Encoder a b) where
  proUnit = Encoder (SCase SUnit SEmpty) (const (EHere EUnit)) (const ())
  (Encoder r1 enc1 dec1) *** (Encoder r2 enc2 dec2) =
    let enc (s1, s2) = prodEval r1 r2 (enc1 s1) (enc2 s2)
        dec = bimap dec1 dec2 . evalToProd r1 r2
    in Encoder (r1 %* r2) enc dec

instance Cocartesian (Encoder a b) where
  proEmpty = Encoder SEmpty absurd absurdEval
  (Encoder r1 enc1 dec1) +++ (Encoder r2 enc2 dec2) =
    let enc = either (inlEval r1 r2 . enc1) (inrEval r1 r2 . enc2)
        dec = bimap dec1 dec2 . evalToSum r1 r2
    in Encoder (r1 %++ r2) enc dec
