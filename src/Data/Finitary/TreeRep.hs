{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE RankNTypes #-}

module Data.Finitary.TreeRep(
  -- * Base Type and its algebra
  Rep, TreeRep(..),
  addRep, multRep, emptyRep, unitRep,

  -- ** Example representations
  idRep, maybeRep,

  -- ** Type-level @Rep@ algebra
  AddRep, MultRep,
  SRep(..), STreeRep(..),
  (%++), (%*), sEmptyRep, sUnitRep, sIdRep,
  KnownRep(..), KnownTreeRep(..),
  withKnownRep, withKnownTreeRep,
  
  -- * Evaluating @Rep@ as a Haskell 'Functor'
  Eval(..), EvalT(..),

  -- ** Correspondence between sums and products of @Rep@ and its evaluation
  fromSum, inlEval, inrEval, toSum,
  fromProduct, toProduct,
  absurdEval, unitEval,

  -- ** Profunctor traversal
  ptraverseEval, ptraverseEvalT,

  -- * Building bidirectional encodings as a @Eval r@ with @Profunctor@
  Encoder(..), idEncoder,
) where

import Data.Kind (Type)

import Data.Bifunctor (Bifunctor(..))
import Data.Void (absurd)
import Data.Functor.Classes ( Eq1(..), Ord1(..), compare1, eq1 )

import Data.Profunctor (Profunctor (..))
import Data.Profunctor.Cartesian
    ( Cartesian(proUnit, (***)), Cocartesian(proEmpty, (+++)) )
import Data.PTraversable

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
--
-- ==== Theories
--
-- @Rep@ can be thought of as a datatype representing
-- a thing called /skew semiring freely generated from one generator/.
-- 
-- Semiring is an abstract algebraic structure with addition and multiplication,
-- but not necessarily have subtraction. Typical instance of semiring is
-- @Integer@ or @Natural@.
--
-- Skew semiring is another abstract algebraic structure similar to semiring:
-- it has addition @+@ and multiplication @*@ with their respective units @0@ and @1@.
-- What differentiates skew semiring is it distinguishes /the order of additions/.
-- In any semiring, @x + y@ and @y + x@ must be equal; but in a skew semiring they can be
-- different.
-- 
-- Formally, a skew semiring is a set @A@ equipped with two binary operations @(+),(*) :: A -> A -> A@
-- and two nullary operations @0,1 :: A@, satisfying following equational axioms:
--
-- - Addition @(A, (+), 0)@ is a monoid
--   - @x + (y + z) === (x + y) + z@
--   - @x + 0 === x === 0 + x@
-- - Multiplication @(A, (*), 1)@ is a monoid
--   - @x * (y * z) === (x * y) * z@
--   - @x * 1 === x === 1 * x@
-- - Multiplication from right distributes to left addition
--   - @0 * z === 0@
--   - @(x + y) * z === (x * z) + (y * z)@
-- 
-- Note that both addition @(+)@ and multiplication @(*)@ are not guaranteed to be commutative,
-- and distributive law exists only for one side.
-- 
-- @Rep@ can be thought of as the free skew semiring on one generator @a@,
-- or in other words the type of normal forms of skew semiring expressions built from
-- @(+,*,0,1)@ and one variable @a@.
--
-- > Rep := 0 | TreeRep + Rep
-- > TreeRep := 1 | a * Rep
type Rep = [TreeRep]


{-

TODO: document /why/ we want to think about skew semiring:

- (Type,Either,(,),Void,()) with order and ≡ as order-preserving iso is a skew semiring
- Same for (Type,Either,(,),Void,()) with enumeration
- (Eval r) represents finitary functor /with these structures/

-}

-- | Representation of a simple (= not a sum of multiple reps)
--   finitary functor.
--
-- - @UnitRep@ represents a unit type: @{UnitRep}(a) = ()@.
-- - @ParRep r@ represents a type with one parameter type prepended:
--   @{ParRep r}(a) = (a, {r}(a))@.
data TreeRep =
    UnitRep
  | ParRep Rep
  deriving (Eq, Ord, Show)

addRep :: Rep -> Rep -> Rep
addRep = (++)

multRep :: Rep -> Rep -> Rep
multRep r1 r2 = concatMap (`multTreeRep` r2) r1

emptyRep :: Rep
emptyRep = []

unitRep :: Rep
unitRep = [UnitRep]

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

-- | 'addRep' at type level
type family AddRep (r1 :: Rep) (r2 :: Rep) :: Rep where
  AddRep '[] r2 = r2
  AddRep (t ': r1) r2 = t : AddRep r1 r2

-- | 'multRep' at type level
type family MultRep (r1 :: Rep) (r2 :: Rep) :: Rep where
  MultRep '[] _ = '[]
  MultRep (UnitRep ': r1) r2 = AddRep r2 (MultRep r1 r2)
  MultRep (ParRep sub1 ': r1) r2 = ParRep (MultRep sub1 r2) ': MultRep r1 r2

-- | Singleton value for type-level @Rep@
data SRep (r :: Rep) where
  SEmpty :: SRep '[]
  SCase :: !(STreeRep t) -> !(SRep r) -> SRep (t ': r)

deriving instance Eq (SRep r)
deriving instance Ord (SRep r)
deriving instance Show (SRep r)

-- | Singleton value for type-level @TreeRep@
data STreeRep (t :: TreeRep) where
  SUnit :: STreeRep 'UnitRep
  SPar :: !(SRep r) -> STreeRep ('ParRep r)

deriving instance Show (STreeRep t)
deriving instance Eq (STreeRep r)
deriving instance Ord (STreeRep r)

-- | Compute the witness of 'AddRep'
(%++) :: SRep r1 -> SRep r2 -> SRep (AddRep r1 r2)
SEmpty %++ sr2 = sr2
SCase st1 sr1 %++ sr2 = SCase st1 (sr1 %++ sr2)

-- | Compute the witness of 'MultRep'
(%*) :: SRep r1 -> SRep r2 -> SRep (MultRep r1 r2)
sr1 %* sr2 = case sr1 of
  SEmpty -> SEmpty
  SCase SUnit sr1' -> sr2 %++ (sr1' %* sr2)
  SCase (SPar ssub1) sr1' -> SCase (SPar (ssub1 %* sr2)) (sr1' %* sr2)

sEmptyRep :: SRep '[]
sEmptyRep = sRep

sUnitRep :: SRep '[ 'UnitRep ]
sUnitRep = sRep

sIdRep :: SRep '[ 'ParRep '[ 'UnitRep ] ]
sIdRep = sRep

{-

TODO: promotion and demotion, and document (add,mult) corresponds
      between (Rep,SRep) using them

withSomeSRep :: Rep -> (forall rep. SRep rep -> result) -> result
demoteSRep :: SRep rep -> Rep

-}

-- ** Class based singleton value creation

class KnownRep (r :: Rep) where
  sRep :: SRep r

class KnownTreeRep (t :: TreeRep) where
  sTreeRep :: STreeRep t

instance KnownRep '[] where
  sRep = SEmpty

instance (KnownTreeRep t, KnownRep r) => KnownRep (t ': r) where
  sRep = SCase sTreeRep sRep

instance KnownTreeRep 'UnitRep where
  sTreeRep = SUnit

instance KnownRep r => KnownTreeRep ('ParRep r) where
  sTreeRep = SPar sRep

withKnownRep :: SRep r -> (KnownRep r => result) -> result
withKnownRep SEmpty body = body
withKnownRep (SCase t r) body =
  withKnownTreeRep t (withKnownRep r body)

withKnownTreeRep :: STreeRep t -> (KnownTreeRep t => result) -> result
withKnownTreeRep SUnit body = body
withKnownTreeRep (SPar r) body = withKnownRep r body

{-

TODO: The current withKnown(Tree)Rep impl. is correct but
*very* inefficient: it basically tears down and reconstructs the
same singleton value.

A trick used in @reflection@ packages like this might work:

> newtype Requires c x = MkRequires (c => x)
> withKnownRep !r body = unsafeCoerce (MkRequires body) r

but I must study about these use of unsafe first.

-}


-----------------------------

-- * Interpreting @Rep@ as a real data type

data Eval (r :: Rep) (a :: Type) where
  EHere :: !(EvalT t a) -> Eval (t ': r) a
  EThere :: !(Eval r a) -> Eval (t ': r) a

data EvalT (t :: TreeRep) (a :: Type) where
  EUnit :: EvalT 'UnitRep a
  EPar :: a -> Eval r a -> EvalT ('ParRep r) a

-- Instances

deriving instance Functor (Eval r)
deriving instance Foldable (Eval r)
deriving instance Traversable (Eval r)

ptraverseEval :: (Cartesian p, Cocartesian p)
  => SRep r -> p a b -> p (Eval r a) (Eval r b)
ptraverseEval r p = case r of
  SEmpty -> lmap absurdEval proEmpty 
  SCase t r' -> dimap splitEval mergeEval (ptraverseEvalT t p +++ ptraverseEval r' p)
  where
    splitEval :: forall t r c.
      Eval (t ': r) c -> Either (EvalT t c) (Eval r c)
    splitEval (EHere x) = Left x
    splitEval (EThere x) = Right x

    mergeEval :: forall t r c.
      Either (EvalT t c) (Eval r c) -> Eval (t ': r) c
    mergeEval = either EHere EThere

ptraverseEvalT :: (Cartesian p, Cocartesian p)
  => STreeRep t -> p a b -> p (EvalT t a) (EvalT t b)
ptraverseEvalT t p = case t of
  SUnit -> rmap (const EUnit) proUnit
  SPar r -> dimap unEPar (uncurry EPar) (p *** ptraverseEval r p)
  where
    unEPar :: forall r c. EvalT (ParRep r) c -> (c, Eval r c)
    unEPar (EPar a x) = (a,x)

instance KnownRep r => PTraversable (Eval r) where
  ptraverseWith from to = dimap from to . ptraverseEval sRep

deriving instance Functor (EvalT t)
deriving instance Foldable (EvalT t)
deriving instance Traversable (EvalT t)

instance KnownTreeRep t => PTraversable (EvalT t) where
  ptraverseWith from to = dimap from to . ptraverseEvalT sTreeRep

instance Eq a => Eq (Eval r a) where
  (==) = eq1

instance Eq1 (Eval r) where
  liftEq eq (EHere x) (EHere y) = liftEq eq x y
  liftEq eq (EThere x) (EThere y) = liftEq eq x y
  -- mismatched constructors
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

unitEval :: Eval '[UnitRep] a
unitEval = EHere EUnit

fromSum :: SRep r1 -> proxy r2 -> Either (Eval r1 x) (Eval r2 x) -> Eval (AddRep r1 r2) x
fromSum r1 r2 = either (inlEval r1 r2) (inrEval r1 r2)

inlEval :: SRep r1 -> proxy r2 -> Eval r1 x -> Eval (AddRep r1 r2) x
inlEval SEmpty _ x = absurdEval x
inlEval (SCase _ r1) r2 x = case x of
  EHere x' -> EHere x'
  EThere x' -> EThere (inlEval r1 r2 x')

inrEval :: SRep r1 -> proxy r2 -> Eval r2 x -> Eval (AddRep r1 r2) x
inrEval SEmpty _ y = y
inrEval (SCase _ r1) r2 y = EThere (inrEval r1 r2 y)

toSum :: SRep r1 -> proxy r2 -> Eval (AddRep r1 r2) x -> Either (Eval r1 x) (Eval r2 x)
toSum SEmpty _r2 z = Right z
toSum (SCase _ r1) r2 z = case z of
  EHere x -> Left (EHere x)
  EThere z' -> first EThere $ toSum r1 r2 z'

fromProduct :: SRep r1 -> SRep r2 -> Eval r1 x -> Eval r2 x -> Eval (MultRep r1 r2) x
fromProduct r1 r2 x y = case r1 of
  SEmpty -> absurdEval x
  SCase SUnit r1' -> case x of
    EHere EUnit -> inlEval r2 (r1' %* r2) y
    EThere x' -> inrEval r2 (r1' %* r2) (fromProduct r1' r2 x' y)
  SCase (SPar sub1) r1' -> case x of
    EHere (EPar a x') -> EHere (EPar a (fromProduct sub1 r2 x' y))
    EThere x' -> EThere (fromProduct r1' r2 x' y)

toProduct :: SRep r1 -> SRep r2 -> Eval (MultRep r1 r2) x -> (Eval r1 x, Eval r2 x)
toProduct r1 r2 z = case r1 of
  SEmpty -> absurdEval z
  SCase SUnit r1' -> case toSum r2 (r1' %* r2) z of
    Left y -> (EHere EUnit, y)
    Right z' -> first EThere $ toProduct r1' r2 z'
  SCase (SPar sub1) r1' -> case z of
    EHere (EPar a z') -> first (EHere . EPar a) $ toProduct sub1 r2 z'
    EThere z' -> first EThere $ toProduct r1' r2 z'

-- * Encoding / Decoding

data Encoder a b s t where
  Encoder :: !(SRep r) -> (s -> Eval r a) -> (Eval r b -> t) -> Encoder a b s t

-- | Encoder for the identity functor.
--
--   It can be used to construct an encoder for arbitrary 'PTraversable'
--   functor using @'ptraverse' 'idEncoder'@.
idEncoder :: Encoder a b a b
idEncoder = Encoder sIdRep idEnc idDec
  where
    idEnc :: c -> Eval '[ParRep '[UnitRep]] c
    idEnc c = EHere (EPar c unitEval)
    
    idDec :: Eval '[ParRep '[UnitRep]] c -> c
    idDec (EHere (EPar c _)) = c
    -- @EThere rest@ case is unnecessary to be
    -- a complete pattern match, because @rest@ has
    -- an uninhabited type @Eval '[] c@.

deriving instance Functor (Encoder a b s)

instance Profunctor (Encoder a b) where
  dimap f g (Encoder rep enc dec) = Encoder rep (enc . f) (g . dec)
  lmap f (Encoder rep enc dec) = Encoder rep (enc . f) dec
  rmap = fmap

instance Cartesian (Encoder a b) where
  proUnit = Encoder (SCase SUnit SEmpty) (const (EHere EUnit)) (const ())
  (Encoder r1 enc1 dec1) *** (Encoder r2 enc2 dec2) =
    let enc (s1, s2) = fromProduct r1 r2 (enc1 s1) (enc2 s2)
        dec = bimap dec1 dec2 . toProduct r1 r2
    in Encoder (r1 %* r2) enc dec

instance Cocartesian (Encoder a b) where
  proEmpty = Encoder SEmpty absurd absurdEval
  (Encoder r1 enc1 dec1) +++ (Encoder r2 enc2 dec2) =
    let enc = either (inlEval r1 r2 . enc1) (inrEval r1 r2 . enc2)
        dec = bimap dec1 dec2 . toSum r1 r2
    in Encoder (r1 %++ r2) enc dec
