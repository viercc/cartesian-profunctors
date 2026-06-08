{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE LambdaCase #-}

-- | A normalized polynomial representation for finitary polynomial functors.
--
-- Compared with "Data.Finitary.TreeRep", this module forgets the
-- syntactic tree structure of sums and products and represents a functor as
--
-- > x^n1 + x^n2 + ... + x^nk
--
-- This is especially useful for Day convolution: monomials satisfy
--
-- > Day x^m x^n ≅ x^(m*n)
--
-- which is implemented by 'DayPoly', 'fromDay', and 'toDay'.
--
-- The list order in 'Poly' is operationally significant in Haskell, but
-- mathematically it should be regarded as a chosen ordering of summands.
module Data.Finitary.PolyRep (
  -- * Base Type and its algebra
  Poly, zeroPoly, addPoly, onePoly, multPoly, parPoly,

  -- ** Type-level @Poly@ algebra
  AddPoly, MultPoly, DayPoly,
  SPoly(..),
  sAddPoly, (%++), sMultPoly, sDayPoly,
  
  KnownPoly(..), withKnownPoly,
  
  -- * Evaluating @Poly@ as a Haskell 'Functor'
  Eval(..),

  -- ** Correspondence between sums, products, and Day convolution of @Poly@ and its evaluation
  absurdEval, unitEval,
  fromSum, inlEval, inrEval, toSum,
  fromProduct, toProduct,
  fromDay, toDay,

  -- ** Profunctor traversal
  ptraverseEval,

  -- * Building bidirectional encodings as a @Eval r@ with @Profunctor@
  Encoder(..), idEncoder
) where

import Data.Kind (Type)

import GHC.TypeNats
import GHC.TypeLits.Witnesses ( (%*), (%+) )
import Data.List.TypeLevel ( type (++) )

import Data.Finite
    ( Finite,
      combineProduct,
      combineSum,
      separateProduct,
      separateSum,
      separateZero, finites )
import Data.Void (absurd)

import Data.Profunctor.Cartesian
import Data.Profunctor (Profunctor(..))
import Data.Bifunctor (Bifunctor(..))
import Data.Type.Equality (TestEquality(..), type (:~:) (..))
import Data.Functor.Day
import Data.Functor.Classes

-- | Finitary polynomial @f(x) = x^e1 + x^e2 + ... + x^en@
--   represented as a list of exponents @[e1, e2, ..., en]@
type Poly = [Nat]

zeroPoly :: Poly
zeroPoly = []

addPoly :: Poly -> Poly -> Poly
addPoly = (++)

onePoly :: Poly
onePoly = [0]

multPoly :: Poly -> Poly -> Poly
multPoly = liftA2 (+)

parPoly :: Poly
parPoly = [1]

type AddPoly :: Poly -> Poly -> Poly
type AddPoly r1 r2 = r1 ++ r2

type family MultPoly1 (e :: Nat) (r2 :: Poly) :: Poly where
  MultPoly1 _ '[] = '[]
  MultPoly1 e (f ': fs) = (e + f) : MultPoly1 e fs

type family MultPoly (r1 :: Poly) (r2 :: Poly) :: Poly where
  MultPoly '[] _ = '[]
  MultPoly (e ': es) r2 = AddPoly (MultPoly1 e r2) (MultPoly es r2)

type family DayPoly1 (e :: Nat) (r2 :: Poly) :: Poly where
  DayPoly1 _ '[] = '[]
  DayPoly1 e (f ': fs) = e * f : DayPoly1 e fs

type family DayPoly (r1 :: Poly) (r2 :: Poly) :: Poly where
  DayPoly '[] _ = '[]
  DayPoly (e ': es) r2 = AddPoly (DayPoly1 e r2) (DayPoly es r2)

data SPoly (r :: Poly) where
  SNil :: SPoly '[]
  SCons :: !(SNat e) -> !(SPoly es) -> SPoly (e ': es)

deriving instance Show (SPoly r)
deriving instance Eq (SPoly r)
deriving instance Ord (SPoly r)

instance TestEquality SPoly where
  testEquality SNil SNil = Just Refl
  testEquality SNil _    = Nothing
  testEquality (SCons se ses) (SCons sf sfs) = do
    Refl <- testEquality se sf
    Refl <- testEquality ses sfs
    Just Refl
  testEquality SCons{} _ = Nothing

sAddPoly, (%++) :: SPoly r1 -> SPoly r2 -> SPoly (AddPoly r1 r2)
sAddPoly = (%++)
SNil %++ sr2 = sr2
SCons se ses %++ sr2 = SCons se (ses %++ sr2)

sMultPoly1 :: SNat e -> SPoly r2 -> SPoly (MultPoly1 e r2)
sMultPoly1 _ SNil = SNil
sMultPoly1 se (SCons sf sfs) = SCons (se %+ sf) (sMultPoly1 se sfs)

sMultPoly :: SPoly r1 -> SPoly r2 -> SPoly (MultPoly r1 r2)
sMultPoly SNil _ = SNil
sMultPoly (SCons se ses) sr2 = sMultPoly1 se sr2 %++ sMultPoly ses sr2

sDayPoly1 :: SNat e -> SPoly r2 -> SPoly (DayPoly1 e r2)
sDayPoly1 _ SNil = SNil
sDayPoly1 se (SCons sf sfs) = SCons (se %* sf) (sDayPoly1 se sfs)

sDayPoly :: SPoly r1 -> SPoly r2 -> SPoly (DayPoly r1 r2)
sDayPoly SNil _ = SNil
sDayPoly (SCons se ses) sr2 = sDayPoly1 se sr2 %++ sDayPoly ses sr2

class KnownPoly (p :: Poly) where
  sPoly :: SPoly p

instance KnownPoly '[] where
  sPoly = SNil

instance (KnownNat e, KnownPoly es) => KnownPoly (e ': es) where
  sPoly = SCons SNat sPoly

withKnownPoly :: SPoly r -> (KnownPoly r => result) -> result
withKnownPoly SNil body = body
withKnownPoly (SCons se ses) body =
  withKnownNat se (withKnownPoly ses body)

{-

[Test]

Define and print f(x) = 1 + x

>>> es = sPoly :: SPoly '[0,1]
>>> es
SCons (SNat @0) (SCons (SNat @1) SNil)

calculate f(x) * f(x) = 1 + x + x + x^2

>>> sMultPoly es es
SCons (SNat @0) (SCons (SNat @1) (SCons (SNat @1) (SCons (SNat @2) SNil)))
>>> sMultPoly es es == (sPoly :: SPoly '[0,1,1,2])
True

-}

data Eval (r :: Poly) (x :: Type) where
  EHere :: !(Finite e -> x) -> Eval (e ': es) x
  EThere :: !(Eval es x) -> Eval (e ': es) x

absurdEval :: Eval '[] a -> b
absurdEval fa = case fa of { }

unitEval :: Eval '[0] a
unitEval = EHere absurdFinite

absurdFinite :: Finite 0 -> b
absurdFinite = absurd . separateZero

deriving instance Functor (Eval r)

{-
TODO: Resolve cyclic import issue and define these instances

instance KnownPoly r => Foldable (Eval r) where
  foldMap = foldMapDefault

instance KnownPoly r => Traversable (Eval r) where
  traverse = traverseDefault

instance KnownPoly r => PTraversable (Eval r) where
  ptraverseWith from to = dimap from to . ptraverseEval sPoly

-}

instance (KnownPoly r, Eq a) => Eq (Eval r a) where
  (==) = eq1

instance (KnownPoly r) => Eq1 (Eval r) where
  liftEq eq = liftEqEval eq sPoly

instance (KnownPoly r, Ord a) => Ord (Eval r a) where
  compare = compare1

instance (KnownPoly r) => Ord1 (Eval r) where
  liftCompare cmp = liftCompareEval cmp sPoly

liftEqEval :: (a -> b -> Bool) -> SPoly r -> Eval r a -> Eval r b -> Bool
liftEqEval _  SNil = absurdEval
liftEqEval eq (SCons se ses) = \case
  EHere vec1 -> \case
    EHere vec2 -> withKnownNat se (liftEqVec eq vec1 vec2)
    _ -> False
  EThere fa -> \case
    EThere fb -> liftEqEval eq ses fa fb
    _ -> False

liftCompareEval :: (a -> b -> Ordering) -> SPoly r -> Eval r a -> Eval r b -> Ordering
liftCompareEval _  SNil = absurdEval
liftCompareEval cmp (SCons se ses) = \case
  EHere vec1 -> \case
    EHere vec2 -> withKnownNat se (liftCompareVec cmp vec1 vec2)
    EThere _ -> LT
  EThere fa -> \case
    EHere _ -> GT
    EThere fb -> liftCompareEval cmp ses fa fb

liftEqVec :: KnownNat n => (a -> b -> Bool) -> (Finite n -> a) -> (Finite n -> b) -> Bool
liftEqVec eq vec1 vec2 = all (\i -> vec1 i `eq` vec2 i) finites

liftCompareVec :: KnownNat n => (a -> b -> Ordering) -> (Finite n -> a) -> (Finite n -> b) -> Ordering
liftCompareVec cmp vec1 vec2 = foldr (\i r -> cmp (vec1 i) (vec2 i) <> r) EQ finites

ptraverseEval :: (Cartesian p, Cocartesian p) => SPoly r -> p a b -> p (Eval r a) (Eval r b)
ptraverseEval SNil _ = lmap absurdEval proEmpty
ptraverseEval (SCons SNat sr) p = dimap splitEval mergeEval (proPower p +++ ptraverseEval sr p)
  where
    splitEval :: forall x xs c. Eval (x ': xs) c -> Either (Finite x -> c) (Eval xs c)
    splitEval (EHere vecX) = Left vecX
    splitEval (EThere fx) = Right fx

    mergeEval :: forall x xs c. Either (Finite x -> c) (Eval xs c) -> Eval (x ': xs) c
    mergeEval = either EHere EThere

-- ** Operators on @(p :: Poly)@ corresponds to those on @Eval p@

fromSum :: SPoly r1 -> proxy r2 -> Either (Eval r1 x) (Eval r2 x) -> Eval (r1 ++ r2) x
fromSum r1 r2 = either (inlEval r1 r2) (inrEval r1 r2)

inlEval :: SPoly r1 -> proxy r2 -> Eval r1 x -> Eval (r1 ++ r2) x
inlEval SNil _ fx = absurdEval fx
inlEval (SCons _ r1) r2 ex = case ex of
  EHere xvec -> EHere xvec
  EThere e1 -> EThere (inlEval r1 r2 e1)

inrEval :: SPoly r1 -> proxy r2 -> Eval r2 x -> Eval (r1 ++ r2) x
inrEval SNil _ gx = gx
inrEval (SCons _ r1) r2 gx = EThere $ inrEval r1 r2 gx

toSum :: SPoly r1 -> proxy r2 -> Eval (r1 ++ r2) x -> Either (Eval r1 x) (Eval r2 x)
toSum SNil _ fx = Right fx
toSum (SCons _ r1) r2 fx = case fx of
  EHere vecX -> Left (EHere vecX)
  EThere fx' -> first EThere $ toSum r1 r2 fx'

fromProduct :: SPoly r1 -> SPoly r2 -> Eval r1 x -> Eval r2 x -> Eval (MultPoly r1 r2) x
fromProduct SNil _ fx _ = absurdEval fx
fromProduct (SCons se ses) r2 fx gx = case fx of
  EHere vecX -> inlEval pLeft pRight (fromProduct1 se r2 vecX gx)
  EThere fx' -> inrEval pLeft pRight (fromProduct ses r2 fx' gx)
  where
    pLeft  = sMultPoly1 se r2
    pRight = sMultPoly ses r2

fromProduct1 :: SNat e -> SPoly r2 -> (Finite e -> x) -> Eval r2 x -> Eval (MultPoly1 e r2) x
fromProduct1 _ SNil _ gx = absurdEval gx
fromProduct1 se (SCons sf sfs) vec1 gx = case gx of
  EHere vec2 -> EHere (appendVec se sf vec1 vec2)
  EThere gx' -> EThere $ fromProduct1 se sfs vec1 gx'

toProduct :: SPoly r1 -> SPoly r2 -> Eval (MultPoly r1 r2) x -> (Eval r1 x, Eval r2 x)
toProduct SNil _ e = absurdEval e
toProduct (SCons se ses) r2 e = case toSum pLeft pRight e of
  Left e1 -> first EHere $ toProduct1 se r2 e1
  Right e2 -> first EThere $ toProduct ses r2 e2
  where
    pLeft  = sMultPoly1 se r2
    pRight = sMultPoly ses r2

toProduct1 :: SNat e -> SPoly r2 -> Eval (MultPoly1 e r2) x -> (Finite e -> x, Eval r2 x)
toProduct1 _ SNil fx = absurdEval fx
toProduct1 se (SCons sf sfs) fx = case fx of
  EHere vecX -> second EHere $ splitVec se sf vecX
  EThere fx'  -> second EThere $ toProduct1 se sfs fx'

appendVec :: SNat n -> SNat m -> (Finite n -> x) -> (Finite m -> x) -> Finite (n + m) -> x
appendVec SNat _ vec1 vec2 = either vec1 vec2 . separateSum

splitVec :: SNat n -> SNat m -> (Finite (n + m) -> x) -> (Finite n -> x, Finite m -> x)
splitVec SNat _ vec =
  let vec' = vec . combineSum
  in (vec' . Left, vec' . Right)

flatVec :: SNat n -> SNat m -> (Finite n -> Finite m -> x) -> Finite (n * m) -> x
flatVec SNat _ vecXY = uncurry vecXY . separateProduct

matVec :: SNat n -> SNat m -> (Finite (n * m) -> x) -> Finite n -> Finite m -> x
matVec SNat _ vec = curry (vec . combineProduct)

fromDay :: SPoly r1 -> SPoly r2 -> Day (Eval r1) (Eval r2) x -> Eval (DayPoly r1 r2) x
fromDay SNil _ (Day fx _ _) = absurdEval fx
fromDay (SCons se ses) r2 (Day fx gy op) = case fx of
  EHere vecX -> inlEval pLeft pRight $ fromDay1 se r2 vecX gy op
  EThere fx' -> inrEval pLeft pRight $ fromDay ses r2 (Day fx' gy op)
  where
    pLeft  = sDayPoly1 se r2
    pRight = sDayPoly ses r2

fromDay1 :: SNat e -> SPoly r2 -> (Finite e -> x) -> Eval r2 y -> (x -> y -> z) -> Eval (DayPoly1 e r2) z
fromDay1 se r2 vecX gy op = case r2 of
  SNil -> absurdEval gy
  SCons sf sfs -> case gy of
    EHere vecY -> EHere $ flatVec se sf (\i j -> op (vecX i) (vecY j))
    EThere gy' -> EThere $ fromDay1 se sfs vecX gy' op

toDay :: SPoly r1 -> SPoly r2 -> Eval (DayPoly r1 r2) x -> Day (Eval r1) (Eval r2) x
toDay SNil _ fx = absurdEval fx
toDay (SCons se ses) r2 fx = case toSum (sDayPoly1 se r2) (sDayPoly ses r2) fx of
  Left fx' -> trans1 EHere $ toDay1 se r2 fx'
  Right fx' -> trans1 EThere $ toDay ses r2 fx'

toDay1 :: SNat e -> SPoly r2 -> Eval (DayPoly1 e r2) x -> Day ((->) (Finite e)) (Eval r2) x
toDay1 _ SNil fx = absurdEval fx
toDay1 se (SCons sf sfs) fx = case fx of
  EHere vec -> Day id (EHere id) (matVec se sf vec)
  EThere fx' -> trans2 EThere $ toDay1 se sfs fx'

data Encoder a b s t where
  Encoder :: !(SPoly r) -> (s -> Eval r a) -> (Eval r b -> t) -> Encoder a b s t

-- | Encoder for the identity functor.
--
--   It can be used to construct an encoder for arbitrary 'Data.PTraversable.PTraversable'
--   functor using
--
--   @
--   'Data.PTraversable.ptraverse' 'idEncoder' :: PTraversable t => Encoder a b (t a) (t b)
--   @
--
--   .
idEncoder :: Encoder a b a b
idEncoder = Encoder sPoly idEnc idDec
  where
    idEnc :: c -> Eval '[1] c
    idEnc c = EHere (const c)
    
    idDec :: Eval '[1] c -> c
    idDec (EHere v) = v minBound
    -- @EThere rest@ case is unnecessary to be
    -- a complete pattern match, because @rest@ has
    -- an uninhabited type @Eval '[] c@.

deriving instance Functor (Encoder a b s)

instance Profunctor (Encoder a b) where
  dimap f g (Encoder rep enc dec) = Encoder rep (enc . f) (g . dec)
  lmap f (Encoder rep enc dec) = Encoder rep (enc . f) dec
  rmap = fmap

instance Cartesian (Encoder a b) where
  proUnit = Encoder (SCons (SNat @0) SNil) (const unitEval) (const ())
  (Encoder r1 enc1 dec1) *** (Encoder r2 enc2 dec2) =
    let enc (s1, s2) = fromProduct r1 r2 (enc1 s1) (enc2 s2)
        dec = bimap dec1 dec2 . toProduct r1 r2
    in Encoder (sMultPoly r1 r2) enc dec

instance Cocartesian (Encoder a b) where
  proEmpty = Encoder SNil absurd absurdEval
  (Encoder r1 enc1 dec1) +++ (Encoder r2 enc2 dec2) =
    let enc = either (inlEval r1 r2 . enc1) (inrEval r1 r2 . enc2)
        dec = bimap dec1 dec2 . toSum r1 r2
    in Encoder (r1 %++ r2) enc dec
