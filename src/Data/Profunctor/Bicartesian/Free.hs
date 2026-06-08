{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImportQualifiedPost #-}

module Data.Profunctor.Bicartesian.Free(
  FreeBicartesian(..),
  liftF, foldFree,

  -- * Utilities
  ProductOp,
  multF
) where

import Data.Profunctor (Profunctor(..), (:->))
import Data.Profunctor.Cartesian
import Data.Bifunctor (Bifunctor(..))
import Data.Profunctor.Monad
import Data.Profunctor.Day

import Data.Profunctor.Cocartesian.Free (FreeCocartesian)
import Data.Profunctor.Cocartesian.Free qualified as CF

-- | Free Bicartesian profunctor (with caveat -- see below) a Cartesian profunctor.
-- 
-- ==== Law issues:
-- 
-- @'FreeBicartesian' p@ can be thought of as a way to add 'Cocartesian' operations
-- on @'Cartesian' p@ by taking "formal sums" of multplie values of @p a b@.
-- 
-- Products on sums of multiple values are normalized to sum of products **as if**
-- it satisfy both left and right /distribution/ laws and /zero/ laws.
-- For example, the result of
-- 
-- @
-- (p1 +++ p2) *** (q1 +++ q2)
-- @
-- 
-- is normalized to
--
-- @
-- (p1 *** q1) +++ (p1 *** q2) +++ (p2 *** q1) +++ (p2 *** q2)
-- @
--
-- up to isomorphisms of parameters of these profunctors.
--
-- Because there are some profunctors which are both @Cartesian@ and @Cocartesian@
-- but do not satisfy distributive laws,
-- interpreting 'FreeBicartesian' into such a profunctor might cause a surprising behavior.
--
-- For example, @'Data.Bifunctor.Joker.Joker' []@ does not satisfy /right distribution/,
-- inheriting @Alternative []@ does not.
-- 
-- >>> import Control.Applicative
-- >>> let x = [id, id]
-- >>> let y = [1]; z = [2]
-- >>> x <*> (y <|> z)
-- [1,2,1,2]
-- >>> (x <*> y) <|> (x <*> z)
-- [1,1,2,2]
-- 
-- With such non-distributive @p@, 'foldFree' does not preserve
-- the @Cartesian@ operations. The following equation does not have to hold.
--
-- @
-- -- Not necessarily holds!
-- foldFree id (ps *** qs)
--  == foldFree id ps *** foldFree id qs
-- @
-- 
-- It is guaranteed that @'foldFree' f@ preserves both @Cartesian@ and
-- @Cocartesian@ operations if it is intepreting into a Bicartesian profunctor,
-- in other words both @Cartesian p@ and @Cocartesian p@ which satisfy these additional laws.
--
-- - @Cocartesian@ instance is commutative
-- - /Left zero/, /Right zero/, /Left distribution/, /Right distribution/
-- 
-- There are no guarantees if any of these conditions are not met. 
newtype FreeBicartesian p a b = FreeBicartesian {
    runFreeBicartesian :: FreeCocartesian p a b
  }
  deriving newtype (Functor, Profunctor, ProfunctorFunctor, ProfunctorMonad, Cocartesian)

liftF :: p a b -> FreeBicartesian p a b
liftF = FreeBicartesian . CF.liftF

-- | Interpret a @FreeBicartesian p@ into a Bicartesian profunction @q@.
--
-- It is guaranteed that @'foldFree' f@ preserves both @Cartesian@ and
-- @Cocartesian@ operations if @q@ is a Bicartesian profunctor.
-- There are no guarantees if any of extra laws to be a Bicartesian are not met. 
foldFree :: (Cartesian q, Cocartesian q) => (p :-> q) -> (FreeBicartesian p :-> q)
foldFree h = CF.foldFree h . runFreeBicartesian

instance Cartesian p => Applicative (FreeBicartesian p a) where
  pure = pureDefault
  liftA2 = liftA2Default

instance Cartesian p => Cartesian (FreeBicartesian p) where
  proUnit = liftF proUnit
  FreeBicartesian ps *** FreeBicartesian qs = FreeBicartesian $ multF (***) ps qs

type ProductOp p q r = forall a1 b1 a2 b2. p a1 b1 -> q a2 b2 -> r (a1,a2) (b1,b2)

multF :: ProductOp p q r -> FreeCocartesian p a b -> FreeCocartesian q a' b' -> FreeCocartesian r (a,a') (b,b')
multF _    (CF.Neutral z) _ = lmap (z . fst) CF.emptyF
multF prod (CF.Cons (Day p ps' opA opB)) qs
  = CF.sumDayF $ Day (distLeftFree prod p qs) (multF prod ps' qs) (distL . first opA) (first opB . undistL)

distLeftFree :: ProductOp p q r -> p a b -> FreeCocartesian q a' b' -> FreeCocartesian r (a,a') (b,b')
distLeftFree _    _ (CF.Neutral z) = lmap (z . snd) CF.emptyF
distLeftFree prod p (CF.Cons (Day q qs' opA opB)) = CF.Cons $ Day (prod p q) (distLeftFree prod p qs') (distR . second opA) (second opB . undistR)
