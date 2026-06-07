{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
module Data.Profunctor.Day(
  Day(..),
  promap1, promap2,
  swapDay, assocDay, unassocDay
) where

import Data.Profunctor (Profunctor (..), (:->))
import Data.Profunctor.Monad (ProfunctorFunctor (..))
import Data.Bifunctor.Assoc (Assoc(..))
import Data.Bifunctor (Bifunctor(..))
import Data.Bifunctor.Swap (Swap (..))

data Day t p q a b where
  Day :: p a1 b1 -> q a2 b2 -> (a -> t a1 a2) -> (t b1 b2 -> b) -> Day t p q a b

deriving instance Functor (Day t p q a)

instance Profunctor (Day t p q) where
    dimap f g (Day p q opA opB) = Day p q (opA . f) (g . opB)

instance ProfunctorFunctor (Day t p) where
    promap = promap2

promap1 :: (p :-> p') -> Day t p q :-> Day t p' q
promap1 h (Day p q opA opB) = Day (h p) q opA opB

promap2 :: (q :-> q') -> Day t p q :-> Day t p q'
promap2 h (Day p q opA opB) = Day p (h q) opA opB

swapDay :: Swap t => Day t p q :-> Day t q p
swapDay (Day p q opA opB) = Day q p (swap . opA) (opB . swap)

assocDay :: Assoc t => Day t (Day t p q) r :-> Day t p (Day t q r)
assocDay (Day (Day p q opA opB) r opC opD) = Day p (Day q r id id) (assoc . first opA . opC) (opD . first opB . unassoc)

unassocDay :: Assoc t => Day t p (Day t q r) :-> Day t (Day t p q) r 
unassocDay (Day p (Day q r opA opB) opC opD) = Day (Day p q id id) r (unassoc . second opA . opC) (opD . second opB . assoc)