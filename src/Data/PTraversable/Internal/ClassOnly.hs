{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
-- | This is **internal** module to break the import cycle.
--   The public API is to use "Data.PTraversable" instead.
module Data.PTraversable.Internal.ClassOnly(
  PTraversable(..),
  ptraverse,

  -- * Specialized traversals
  foldMapDefault,
  fmapDefault,
  traverseDefault,
  enum1,
  coenum1,
  cardinality1,

  -- * Default Eq/Ord
  liftEq',
  liftEqDefault,
  eq1Default,
  liftCompare',
  liftCompareDefault,
  compare1Default
) where

import Data.Profunctor.Cartesian (Cartesian, Cocartesian)
import Data.Functor.Classes (Ord1)
import Control.Applicative (Alternative)
import Data.Functor.Contravariant.Divisible (Divisible, Decidable)
import Data.Profunctor (Forget(..), Star (..))
import Data.Bifunctor.Joker (Joker(..))
import Data.Bifunctor.Clown (Clown(..))
import Data.Functor.Contravariant (Equivalence(..), Comparison (..))
import Data.Profunctor.Counting (Counting(..))

class (Ord1 t, Traversable t) => PTraversable t where
  {-# MINIMAL ptraverseWith #-}
  ptraverseWith ::
    (Cartesian p, Cocartesian p) =>
    (as -> t a) ->
    (t b -> bs) ->
    p a b ->
    p as bs

ptraverse :: forall t p a b. (PTraversable t, Cartesian p, Cocartesian p) => p a b -> p (t a) (t b)
ptraverse = ptraverseWith id id
{-# INLINEABLE ptraverse #-}

fmapDefault :: (PTraversable t) => (a -> b) -> t a -> t b
fmapDefault = ptraverse
{-# INLINEABLE fmapDefault #-}

foldMapDefault :: (PTraversable t, Monoid m) => (a -> m) -> t a -> m
foldMapDefault = runForget . ptraverse . Forget
{-# INLINEABLE foldMapDefault #-}

traverseDefault :: (PTraversable t, Applicative f) => (a -> f b) -> t a -> f (t b)
traverseDefault = runStar . ptraverse . Star
{-# INLINEABLE traverseDefault #-}

enum1 :: (PTraversable t, Alternative f) => f a -> f (t a)
enum1 = runJoker . ptraverse . Joker
{-# INLINEABLE enum1 #-}

coenum1 :: (PTraversable t, Divisible f, Decidable f) => f b -> f (t b)
coenum1 = runClown . ptraverse . Clown
{-# INLINEABLE coenum1 #-}

cardinality1 :: forall t proxy. (PTraversable t) => proxy t -> Int -> Int
cardinality1 _ = getCounting . ptraverse @t . Counting
{-# INLINEABLE cardinality1 #-}

-- | Type-restricted version of 'Data.Functor.Classes.liftEq'.
--
-- @
-- liftEq  :: forall t a b. (Eq1 t) => (a -> b -> Bool) -> t a -> t b -> Bool
-- liftEq' :: forall t a.   (.....) => (a -> a -> Bool) -> t a -> t a -> Bool
-- @
liftEq' :: (PTraversable t) => (a -> a -> Bool) -> t a -> t a -> Bool
liftEq' = getEquivalence . coenum1 . Equivalence
{-# INLINEABLE liftEq' #-}

liftEqDefault :: (PTraversable t) => (a -> b -> Bool) -> t a -> t b -> Bool
liftEqDefault eq ta tb = eqEithers (Left <$> ta) (Right <$> tb)
  where
    eqEithers = getEquivalence . coenum1 $ Equivalence eq'
    eq' (Left _) (Left _) = error "liftEqDefault: should be unreachable here"
    eq' (Right _) (Right _) = error "liftEqDefault: should be unreachable here"
    eq' (Left a) (Right b) = eq a b
    eq' (Right b) (Left a) = eq a b

eq1Default :: (PTraversable t, Eq a) => t a -> t a -> Bool
eq1Default = liftEq' (==)
{-# INLINEABLE eq1Default #-}

-- | Type-restricted version of 'Data.Functor.Classes.liftCompare'.
--
-- @
-- liftEq  :: forall t a b. (Eq1 t) => (a -> b -> Bool) -> t a -> t b -> Bool
-- liftEq' :: forall t a.   (.....) => (a -> a -> Bool) -> t a -> t a -> Bool
-- @
liftCompare' :: (PTraversable t) => (a -> a -> Ordering) -> t a -> t a -> Ordering
liftCompare' = getComparison . coenum1 . Comparison
{-# INLINEABLE liftCompare' #-}

compare1Default :: (PTraversable t, Ord a) => t a -> t a -> Ordering
compare1Default = liftCompare' compare
{-# INLINEABLE compare1Default #-}

liftCompareDefault :: (PTraversable t) => (a -> b -> Ordering) -> t a -> t b -> Ordering
liftCompareDefault cmp ta tb = cmpEithers (Left <$> ta) (Right <$> tb)
  where
    cmpEithers = liftCompare' cmp'
    cmp' (Left _) (Left _) = error "liftCompareDefault: should be unreachable here"
    cmp' (Right _) (Right _) = error "liftCompareDefault: should be unreachable here"
    cmp' (Left a) (Right b) = cmp a b
    cmp' (Right b) (Left a) = case cmp a b of
      EQ -> EQ
      LT -> GT
      GT -> LT
