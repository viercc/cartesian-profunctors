{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
-- This module provides Generics-related instances for
-- PTraversable.
-- Since they are defined in Data.PTraversable.Internal.ClassOnly,
-- they are orphans instances, but that is expected.
{-# OPTIONS_GHC -Wno-orphans #-}

-- | This is **internal** module to break the import cycle.
--   The public API is to use "Data.PTraversable" instead.
module Data.PTraversable.Internal.Generics
  (
  -- Instance only; no exported names
  )
where

import Data.Coerce (coerce)
import Data.Finitary.Enum (Enum, describeEnum)
import Data.PTraversable.Internal.ClassOnly
import Data.Profunctor (Profunctor (..))
import Data.Profunctor.Cartesian
import Data.Profunctor.Unsafe ((#.), (.#))
import GHC.Generics
import GHC.Generics.Orphans ()
import Prelude hiding (Enum)

unGenerically1 :: Generically1 f a -> f a
unGenerically1 = coerce
{-# INLINEABLE unGenerically1 #-}

instance (Generic1 t, PTraversable (Rep1 t)) => PTraversable (Generically1 t) where
  ptraverseWith f g = ptraverseWith (from1 . unGenerically1 . f) (g . Generically1 . to1)
  {-# INLINEABLE ptraverseWith #-}

---- Generics ----

instance PTraversable V1 where
  ptraverseWith f _ _ = lmap (absurdV1 . f) proEmpty
  {-# INLINEABLE ptraverseWith #-}

absurdV1 :: V1 a -> b
absurdV1 v = case v of {}

instance PTraversable U1 where
  ptraverseWith _ g _ = rmap (const (g U1)) proUnit
  {-# INLINEABLE ptraverseWith #-}

instance PTraversable Par1 where
  ptraverseWith :: forall p a b as bs. (Cartesian p, Cocartesian p) => (as -> Par1 a) -> (Par1 b -> bs) -> p a b -> p as bs
  ptraverseWith = coerce (dimap :: (as -> a) -> (b -> bs) -> p a b -> p as bs)
  {-# INLINEABLE ptraverseWith #-}

instance (Enum c) => PTraversable (K1 i c) where
  ptraverseWith f g _ = dimap (unK1 #. f) (g .# K1) describeEnum

instance (PTraversable f) => PTraversable (M1 i c f) where
  ptraverseWith f g = ptraverseWith (unM1 . f) (g . M1)
  {-# INLINEABLE ptraverseWith #-}

instance (PTraversable f) => PTraversable (Rec1 f) where
  ptraverseWith f g = ptraverseWith (unRec1 . f) (g . Rec1)
  {-# INLINEABLE ptraverseWith #-}

instance (PTraversable t, PTraversable u) => PTraversable (t :+: u) where
  ptraverseWith f g p = dimap f' g' $ ptraverse p +++ ptraverse p
    where
      f' as = case f as of
        L1 ta -> Left ta
        R1 ua -> Right ua
      g' = either (g . L1) (g . R1)
  {-# INLINEABLE ptraverseWith #-}

instance (PTraversable f, PTraversable g) => PTraversable (f :*: g) where
  ptraverseWith f g p = dimap f' g' $ ptraverse p *** ptraverse p
    where
      f' as = case f as of
        ta :*: ua -> (ta, ua)
      g' (ta, ua) = g (ta :*: ua)
  {-# INLINEABLE ptraverseWith #-}

instance
  (PTraversable t, PTraversable u) =>
  PTraversable (t :.: u)
  where
  ptraverseWith f g = ptraverseWith (unComp1 . f) (g . Comp1) . ptraverse
  {-# INLINEABLE ptraverseWith #-}
