{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Data.Profunctor.Cartesian.Free(
    -- * The free 'Cartesian' profunctor
    FreeCartesian(..),
    liftF,
    foldFree,

    -- * Newtype wrapper
    ForgetCartesian(..),
) where

import Data.Profunctor (Profunctor(..), (:->))
import Data.Profunctor.Monad
import Data.Profunctor.Cartesian
import Data.Profunctor.Day

-- * The free 'Cartesian' profunctor

-- | The free 'Cartesian' profunctor.
data FreeCartesian p a b =
    Neutral b
  | Cons (Day (,) p (FreeCartesian p) a b)
  deriving Functor

instance Applicative (FreeCartesian p a) where
  pure = pureDefault
  liftA2 = liftA2Default

instance Profunctor (FreeCartesian p) where
  dimap _ g (Neutral b) = Neutral (g b)
  dimap f g (Cons ps')  = Cons (dimap f g ps')

prodDayF :: Day (,) (FreeCartesian p) (FreeCartesian p) :-> FreeCartesian p
prodDayF (Day (Neutral b) qs opA opB) = dimap (snd . opA) (curry opB b) qs
prodDayF (Day (Cons ps) qs opA opB) = Cons $ promap2 prodDayF $ assocDay (Day ps qs opA opB)

instance Cartesian (FreeCartesian p) where
    proUnit = Neutral ()
    proProduct opA opB p q = prodDayF (Day p q opA opB)

liftF :: p :-> FreeCartesian p
liftF p = Cons $ Day p proUnit (, ()) fst

foldFree :: Cartesian q => (p :-> q) -> FreeCartesian p :-> q
foldFree _ (Neutral b) = rmap (const b) proUnit
foldFree handle (Cons ps) = prodDay handle (foldFree handle) ps

instance ProfunctorFunctor FreeCartesian where
  promap pq ps = case ps of
    Neutral b -> Neutral b
    Cons (Day p ps' opA opB) -> Cons (Day (pq p) (promap pq ps') opA opB)

instance ProfunctorMonad FreeCartesian where
  proreturn = liftF
  projoin = foldFree id

-- | Forgets 'Cartesian' instance from a 'Profunctor'.
newtype ForgetCartesian p a b = ForgetCartesian { recallCartesian :: p a b }
  deriving newtype (Functor, Profunctor, Cocartesian)
  -- DO NOT add "deriving Cartesian" clause!
