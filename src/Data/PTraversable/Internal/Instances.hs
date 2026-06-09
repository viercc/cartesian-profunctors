{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
-- This module provides non-Generics-related instances for
-- PTraversable.
-- Since they are defined in Data.PTraversable.Internal.ClassOnly,
-- they are orphans instances, but that is expected.
{-# OPTIONS_GHC -Wno-orphans #-}

module Data.PTraversable.Internal.Instances (
  WrappedPTraversable(..)
) where

import Prelude hiding (Enum)
import Data.Finitary.Enum (Enum (..))
import Data.Profunctor.FinFn (withFinFn)

import Data.Coerce (coerce)
import Data.Functor.Classes (Eq1 (..), Ord1 (..))
import GHC.Generics (Generically1 (..))

import Data.Functor.Compose (Compose)
import Data.Functor.Identity (Identity)
import Data.Functor.Product (Product)
import Data.Functor.Sum (Sum)

import Data.PTraversable.Internal.ClassOnly
import Data.PTraversable.Internal.Generics ()

newtype WrappedPTraversable t a = WrapPTraversable {unwrapPTraversable :: t a}
  deriving (PTraversable) via t

instance (Eq a, PTraversable t) => Eq (WrappedPTraversable t a) where
  (==) = eq1Default

instance (PTraversable t) => Eq1 (WrappedPTraversable t) where
  liftEq = liftEqDefault

instance (Ord a, PTraversable t) => Ord (WrappedPTraversable t a) where
  compare = compare1Default

instance (PTraversable t) => Ord1 (WrappedPTraversable t) where
  liftCompare = liftCompareDefault

instance (Enum a, PTraversable t) => Enum (WrappedPTraversable t a) where
  enumeration = ptraverseWith unwrapPTraversable WrapPTraversable enumeration
  withEnum = withFinFn enumeration

instance (PTraversable t) => Functor (WrappedPTraversable t) where
  fmap f = coerce (fmapDefault @t f)

instance (PTraversable t) => Foldable (WrappedPTraversable t) where
  foldMap f = coerce (foldMapDefault @t f)

instance (PTraversable t) => Traversable (WrappedPTraversable t) where
  traverse f = fmap WrapPTraversable . traverseDefault @t f . coerce

-- Orphan Instances --

deriving via (Generically1 Identity) instance PTraversable Identity

deriving via (Generically1 Maybe) instance PTraversable Maybe

deriving via
  (Generically1 ((,) a))
  instance
    (Enum a) => PTraversable ((,) a)

deriving via
  (Generically1 (Either a))
  instance
    (Enum a) => PTraversable (Either a)

deriving via
  (Generically1 (Sum t u))
  instance
    (PTraversable t, PTraversable u) => PTraversable (Sum t u)

deriving via
  (Generically1 (Product t u))
  instance
    (PTraversable t, PTraversable u) => PTraversable (Product t u)

deriving via
  (Generically1 (Compose t u))
  instance
    (PTraversable t, PTraversable u) => PTraversable (Compose t u)
