{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TupleSections #-}
module Data.Profunctor.Cartesian(
  Cartesian(..),
  prodDay,

  Cocartesian(..),
  sumDay,
  
  -- * @Cartesian p@ iff @forall x. Applicative (p x)@
  pureDefault,
  proUnitDefault,
  liftA2Default,
  fanoutDefault,

  -- * Utilities
  describeFinite,
  describeFiniteBits,

  -- * Laws
  
  -- ** 'Cartesian' laws
  
  -- $cartesian_laws
  
  -- ** 'Cocartesian' laws
  
  -- $cocartesian_laws
  
  -- ** Optional laws for interaction of @Cartesian@ and @Cocartesian@
  
  -- $bicartesian_laws

  -- * Type isomorphisms
  -- ** Re-exports
  Assoc(..), Swap(..),
  -- ** Unit laws
  unitL, ununitL, unitR, ununitR,
  emptyL, unemptyL, emptyR, unemptyR,
  -- ** Distributivity 
  distL, undistL, distR, undistR,
) where

import Control.Applicative

import Data.Void

import Data.Functor.Contravariant.Divisible
import Data.Bifunctor(Bifunctor(..))
import Data.Bifunctor.Assoc ( Assoc(..) )
import Data.Bifunctor.Swap (Swap(..))
import Data.Bifunctor.Clown
import Data.Bifunctor.Joker
import Data.Bifunctor.Product
import Data.Profunctor
import Data.Profunctor.Monad
import Data.Profunctor.Yoneda
import Data.Profunctor.Composition hiding (assoc)
import Data.Profunctor.Day

import Data.Bits
import GHC.TypeNats ( KnownNat, Natural, natVal )
import Data.Finite (Finite, getFinite, finites)
import Data.Finite.Internal qualified as Unsafe

class Profunctor p => Cartesian p where
  {-# MINIMAL proUnit, (proProduct | (***) | (&&&)) #-}

  -- | Unit of the product.
  --
  -- The type of 'proUnit' can be understood as @proUnit' :: p () ()@
  -- treated to have more generally-typed @p a ()@ using 'lmap'.
  -- 
  -- @
  -- const () :: a -> ()
  -- proUnit' :: p () ()
  -- 'lmap' (const ()) proUnit' :: p a ()
  -- @
  proUnit :: p a ()
  
  proProduct :: (a -> (a1,a2)) -> ((b1, b2) -> b) -> p a1 b1 -> p a2 b2 -> p a b
  proProduct f g p q = dimap f g $ p *** q
  
  -- | Product of two profunctors
  (***) :: p a b -> p a' b' -> p (a,a') (b,b')
  p *** q = lmap fst p &&& lmap snd q
  
  -- | Alternative way to define the product (pronounced \"fan-out\")
  (&&&) :: p a b -> p a b' -> p a (b, b')
  (&&&) = proProduct delta id

  -- | Function from finite types can be constructed as iterated product.
  --
  -- There is a default implementaion, but it can be more efficient implementation.
  proPower :: KnownNat n => p a b -> p (Finite n -> a) (Finite n -> b)
  proPower = runPower describeFinite

{- $cartesian_laws

Instances of 'Cartesian' must satisfy the following equations.

[Left unit of @'***'@]
  @dimap 'ununitL' 'unitL' ('proUnit' *** p) === p@

[Right unit of @***@]
  @dimap 'ununitR' 'unitR' (p *** 'proUnit') === p@

[Associativity of @***@]
  @dimap 'assoc' 'unassoc' ((p *** q) *** r) === p *** (q *** r)@

Some instance of @Cartesian@ optionally satisfy the following equation.

[Commutativity of @***@]
  @dimap 'Data.Bifunctor.Swap.swap' swap (p *** q) === q *** p@

In this library, an instance of @Cartesian@ is called commutative @Cartesian@
if it satisfy the above /commutativity/ law.

==== Instances with and without commutativity

TODO fill here: most instance is not commutative, @Counting@ or @Forget r@ for commutative monoid is (positive)

-}

delta :: a -> (a,a)
delta a = (a,a)

prodDay :: Cartesian r => (p :-> r) -> (q :-> r) -> Day (,) p q :-> r
prodDay pr qr (Day p q opA opB) = proProduct opA opB (pr p) (qr q)

-- * @Cartesian p@ iff @forall x. Applicative (p x)@

pureDefault :: Cartesian p => b -> p a b
pureDefault b = rmap (const b) proUnit

proUnitDefault :: Applicative (p a) => p a ()
proUnitDefault = pure ()

liftA2Default :: Cartesian p => (a -> b -> c) -> p x a -> p x b -> p x c
liftA2Default f = proProduct delta (uncurry f)

fanoutDefault :: (Profunctor p, Applicative (p a)) => p a b1 -> p a b2 -> p a (b1, b2)
fanoutDefault = liftA2 (,)

instance Cartesian (->) where
  proUnit = const ()
  p1 *** p2 = bimap p1 p2
  proPower = (.)

instance (Monoid r) => Cartesian (Forget r) where
  proUnit = Forget (const mempty)
  Forget f *** Forget g = Forget (\(a,b) -> f a <> g b)
  proPower (Forget f) = Forget (\h -> foldMap (f . h) finites)

instance (Applicative f) => Cartesian (Star f) where
  proUnit = Star (const (pure ()))
  Star p1 *** Star p2 = Star $ \(a,a') -> liftA2 (,) (p1 a) (p2 a')

instance (Applicative f) => Cartesian (Joker f) where
  proUnit = Joker (pure ())
  Joker p1 *** Joker p2 = Joker $ liftA2 (,) p1 p2

instance (Divisible f) => Cartesian (Clown f) where
  proUnit = Clown conquer
  Clown p1 *** Clown p2 = Clown $ divided p1 p2

instance (Cartesian p, Cartesian q) => Cartesian (Product p q) where
  proUnit = Pair proUnit proUnit
  Pair p1 q1 *** Pair p2 q2 = Pair (p1 *** p2) (q1 *** q2)
  proPower (Pair p q) = Pair (proPower p) (proPower q)

instance (Cartesian p, Cartesian q) => Cartesian (Procompose p q) where
  proUnit = Procompose proUnit proUnit
  Procompose p1 q1 *** Procompose p2 q2 =
    Procompose (p1 *** p2) (q1 *** q2)
  proPower (Procompose p q) = Procompose (proPower p) (proPower q)

instance (Cartesian p) => Cartesian (Yoneda p) where
  proUnit = proreturn proUnit
  p *** q = proreturn (proextract p *** proextract q)

instance (Cartesian p) => Cartesian (Coyoneda p) where
  proUnit = proreturn proUnit
  Coyoneda l1 r1 p *** Coyoneda l2 r2 q
    = Coyoneda (l1 *** l2) (r1 *** r2) (p *** q)

class Profunctor p => Cocartesian p where
  {-# MINIMAL proEmpty, (proSum | (+++) | (|||)) #-}

  -- | Unit of the sum.
  --
  -- The type of 'proEmpty' can be understood as @proEmpty' :: p Void 'Void'@
  -- treated to have more generally-typed @p Void b@ using 'rmap'.
  -- 
  -- @
  -- 'absurd'    :: Void -> b
  -- proEmpty' :: p Void Void
  -- 'rmap' absurd proEmpty' :: p Void b
  -- @
  proEmpty :: p Void b
  
  proSum :: (a -> Either a1 a2) -> (Either b1 b2 -> b) -> p a1 b1 -> p a2 b2 -> p a b
  proSum f g p q = dimap f g (p +++ q)

  -- | Sum of two profunctors
  (+++) :: p a b -> p a' b' -> p (Either a a') (Either b b')
  p +++ q = rmap Left p ||| rmap Right q

  -- | Alternative way to define the sum (pronounced \"fan-in\")
  (|||) :: p a b -> p a' b -> p (Either a a') b
  (|||) = proSum id nabla

  -- | Pairing with finite types can be constructed as iterated sum.
  --
  -- There is a default implementaion, but it can be more efficient implementation.
  proTimes :: KnownNat n => p a b -> p (Finite n, a) (Finite n, b)
  proTimes = runCopower describeFinite

{- $cocartesian_laws

Instances of 'Cocartesian' must satisfy the following equations.

[Left unit of @'+++'@]
  @dimap 'unemptyL' 'emptyL' ('proEmpty' +++ p) === p@

[Right unit of @+++@]
  @dimap 'unemptyR' 'emptyR' (p +++ 'proEmpty') === p@

[Associativity of @+++@]
  @dimap 'assoc' 'unassoc' ((p +++ q) +++ r) === p +++ (q +++ r)@

Some instance of @Cocartesian@ optionally satisfy the following equation.

[Commutativity of @+++@]
  @dimap 'swap' swap (p +++ q) === q +++ p@

In this library, an instance of @Cocartesian@ is called commutative @Cocartesian@
if it satisfy the above /commutativity/ law.

==== Instances with and without commutativity

TODO fill here: @Star f@, @Clown Equivalence@ (positive) and
  @Clown Comparison@, @Alternative f => Joker f@ (negative)

-}

nabla :: Either a a -> a
nabla = either id id

sumDay :: Cocartesian r => (p :-> r) -> (q :-> r) -> Day Either p q :-> r
sumDay pr qr (Day p q opA opB) = proSum opA opB (pr p) (qr q)

instance Cocartesian (->) where
  proEmpty = absurd
  p1 +++ p2 = bimap p1 p2
  proTimes = second

instance Cocartesian (Forget r) where
  proEmpty = Forget absurd
  Forget f +++ Forget g = Forget (either f g)
  proTimes (Forget f) = Forget (f . snd)

instance (Functor f) => Cocartesian (Star f) where
  proEmpty = Star absurd
  Star p1 +++ Star p2 = Star $ either (fmap Left . p1) (fmap Right . p2)
  proTimes (Star p) = Star $ \(i,a) -> (i,) <$> p a

instance (Alternative f) => Cocartesian (Joker f) where
  proEmpty = Joker empty
  Joker p1 +++ Joker p2 = Joker $ (Left <$> p1) <|> (Right <$> p2)

instance (Decidable f) => Cocartesian (Clown f) where
  proEmpty = Clown lost
  Clown p1 +++ Clown p2 = Clown $ chosen p1 p2

instance (Cocartesian p, Cocartesian q)
       => Cocartesian (Product p q) where
  proEmpty = Pair proEmpty proEmpty
  Pair p1 q1 +++ Pair p2 q2 = Pair (p1 +++ p2) (q1 +++ q2)
  proTimes (Pair p q) = Pair (proTimes p) (proTimes q)

instance (Cocartesian p, Cocartesian q)
       => Cocartesian (Procompose p q) where
  proEmpty = Procompose proEmpty proEmpty
  Procompose p1 q1 +++ Procompose p2 q2 = Procompose (p1 +++ p2) (q1 +++ q2)
  proTimes (Procompose p q) = Procompose (proTimes p) (proTimes q)

instance (Cocartesian p) => Cocartesian (Yoneda p) where
  proEmpty = proreturn proEmpty
  p +++ q = proreturn (proextract p +++ proextract q)

instance (Cocartesian p) => Cocartesian (Coyoneda p) where
  proEmpty = proreturn proEmpty
  Coyoneda l1 r1 p +++ Coyoneda l2 r2 q
    = Coyoneda (l1 +++ l2) (r1 +++ r2) (p +++ q)

{- $bicartesian_laws

If a @Profunctor p@ is an instance of both @Cartesian@ and @Cocartesian@,
there are few named properties they optionally satisfy.

[Left zero]
  @dimap absurd (absurd . fst) (proEmpty *** p) === proEmpty@

[Left distribution]
  @dimap 'undistL' 'distL' ((p +++ q) *** r) === (p *** r) +++ (q *** r)@

[Right zero]
  @dimap absurd (absurd . snd) (p *** proEmpty) === proEmpty@

[Right distribution]
  @dimap 'undistR' 'distR' (r *** (p +++ q)) === (r *** p) +++ (r *** q)@

In this library, an instance of both @Cartesian@ and @Cocartesian@ is called

- near-Bicartesian if it additionally satisfy /Left zero/ and /Left distribution/
- Bicartesian if it is near-Bicartesian, is /commutative/ @Cocartesian@, and satisfy all four of
  /Right zero/ and /Right distribution/. In other words,
  satisfy all of above four laws and commutativity of @+++@.

==== Instances with/without optional properties

TODO fill here

==== Note:

In usual mathematical abstract algebra context,
it is common practice to name /Right distributivity/ to mean
Left zero and Left distibution combined,
and same switching for /Left distributivity/.

The naming convention of this library came from /Haskell/ convention
of describing distributive properties of 'Control.Applicative.Alternative'
and 'Control.Monad.MonadPlus'.

<https://wiki.haskell.org/index.php?title=Typeclassopedia#Laws_6>

-}

unitL :: ((),a) -> a
unitL = snd

ununitL :: a -> ((), a)
ununitL = ((),)

unitR :: (a,()) -> a
unitR = fst

ununitR :: a -> (a, ())
ununitR = (,())

emptyL :: Either Void a -> a
emptyL = either absurd id

unemptyL :: a -> Either Void a
unemptyL = Right

emptyR :: Either a Void -> a
emptyR = either id absurd

unemptyR :: a -> Either a Void
unemptyR = Left

distL :: (Either a b, c) -> Either (a,c) (b,c)
distL (Left a, c) = Left (a,c)
distL (Right b, c) = Right (b,c)

undistL :: Either (a,c) (b,c) -> (Either a b, c)
undistL (Left (a,c)) = (Left a, c)
undistL (Right (b,c)) = (Right b, c)

distR :: (c, Either a b) -> Either (c,a) (c,b)
distR = bimap swap swap . distL . swap

undistR :: Either (c,a) (c,b) -> (c, Either a b)
undistR = swap . undistL . bimap swap swap

--

newtype Power p a b = Power { runPower :: forall s t. p s t -> p (b -> s) (a -> t) }

instance Profunctor p => Profunctor (Power p) where
    dimap f g (Power k) = Power (dimap (. g) (. f) . k)

instance Profunctor p => Cartesian (Power p) where
    proUnit = Power $ dimap ($ ()) const
    ep *** eq = Power $ \e -> dimap curry uncurry $ runPower ep (runPower eq e)

instance Cartesian p => Cocartesian (Power p) where
    proEmpty = Power $ \_ -> dimap id (const absurd) proUnit
    ep +++ eq = Power $ \e -> proProduct (\f -> (f . Left, f . Right)) (uncurry either) (runPower ep e) (runPower eq e)
    proTimes p = Power $ \e -> dimap curry uncurry $ proPower (runPower p e)

--

newtype Copower p a b = Copower { runCopower :: forall s t. p s t -> p (a,s) (b,t) }

instance Profunctor p => Profunctor (Copower p) where
  dimap f g (Copower k) = Copower $ \p -> dimap (first f) (first g) (k p)

instance Profunctor p => Cartesian (Copower p) where
  proUnit = Copower $ \p -> dimap snd ((),) p
  cp *** cq = Copower $ \p -> dimap assoc unassoc $ runCopower cp (runCopower cq p)

instance Cocartesian p => Cocartesian (Copower p) where
  proEmpty = Copower $ \_ -> dimap fst absurd proEmpty
  p +++ q = Copower $ \c -> proSum distrib undistrib (runCopower p c) (runCopower q c)
    where
      distrib (ab,c) = bimap (,c) (,c) ab
      undistrib = either (first Left) (first Right)
  proTimes p = Copower $ \c -> dimap assoc unassoc $ proTimes (runCopower p c)

--

describeFinite :: forall n p. (KnownNat n, Cartesian p, Cocartesian p) => p (Finite n) (Finite n)
describeFinite = dimap finiteToNatural unsafeNaturalToFinite (dNatural (natVal @n undefined))
  where
    finiteToNatural = fromInteger . getFinite
    unsafeNaturalToFinite = Unsafe.Finite . toInteger

dNatural :: (Cartesian p, Cocartesian p) => Natural -> p Natural Natural
dNatural 0 = dimap (error "here no value should come") absurd proEmpty
dNatural 1 = dimap (const ()) (const 0) proUnit
dNatural 2 = dBit
dNatural n = case n `divMod` 2 of
  (n',0) -> proProduct div2 undiv2 (dNatural n') dBit
  (n',_) -> proSum unshiftNat shiftNat proUnit (proProduct div2 undiv2 (dNatural n') dBit)
  where
    div2 x = x `divMod` 2
    undiv2 (q,r) = 2 * q + r
    unshiftNat 0 = Left ()
    unshiftNat x = Right (pred x)
    shiftNat = either (const 0) succ

describeFiniteBits :: forall a p. (FiniteBits a, Cartesian p, Cocartesian p) => p a a
describeFiniteBits = dBits (finiteBitSize (zeroBits :: a))

dBit :: (Bits a, Cartesian p, Cocartesian p) => p a a
dBit = proSum i2b b2i proUnit proUnit
  where
    i2b x = if testBit x 0 then Right () else Left ()
    b2i (Left _) = zeroBits
    b2i (Right _)  = bit 0

dBits :: (Bits a, Cartesian p, Cocartesian p) => Int -> p a a
dBits n
  | n <= 0 = error "bad!"
  | n == 1 = dBit
  | otherwise =
      case separate n of
        (0, p) -> dBitsPow2 p
        (m, p) ->
          let l x = (x `shiftR` p, x)
              r (a,b) = a `shiftL` p .|. b
          in dimap l r $ dBits m *** dBitsPow2 p

separate :: Int -> (Int, Int)
-- must be x > 1
separate x = (r, bit p)
  where
    p = finiteBitSize (0 :: Int) - countLeadingZeros x - 1
    r = clearBit x p

dBitsPow2 :: (Bits a, Cartesian p, Cocartesian p) => Int -> p a a
dBitsPow2 1 = dBit
dBitsPow2 n =
  let m = n `div` 2
      halfBits = dBitsPow2 m
      l x = (x `shift` (-m), x)
      r (a,b) = a `shift` m .|. b
  in dimap l r $ halfBits *** halfBits

