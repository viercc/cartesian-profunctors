# Laws for `Cartesian` and `Cocartesian`

This document is a draft discussing what equational laws should be imposed on
instances of `Cartesian` and `Cocartesian`.

---

## Background

`Cartesian` and `Cocartesian` are profunctor type classes that structure how a
profunctor `p a b` interacts with the product `(,)` and coproduct `Either` of
Haskell types, respectively. Their operations are:

```haskell
class Profunctor p => Cartesian p where
  proUnit   :: p a ()
  (***)     :: p a b -> p a' b' -> p (a,a') (b,b')

class Profunctor p => Cocartesian p where
  proEmpty  :: p Void b
  (+++)     :: p a b -> p a' b' -> p (Either a a') (Either b b')
```

The intended reading:
- `proUnit` is the "trivial" observation: any input can be "forgotten" to yield `()`.
- `(***)` combines two profunctors to observe/produce a pair.
- `proEmpty` is the "impossible" case: no value of type `Void` can arrive.
- `(+++)` combines two profunctors to handle either branch of a sum.

The natural mathematical context is a **(lax) monoidal profunctor**: `p` should
be compatible with the monoidal structure `(,)` (for `Cartesian`) or `Either`
(for `Cocartesian`) on `Hask`.

---

## Structural isomorphisms

The laws are stated up to the standard structural isomorphisms of `(,)` and
`Either`:

```haskell
-- Product
unitL  :: ((), a) -> a;              unitL  = snd
unitL' :: a -> ((), a);              unitL' = ((),)
unitR  :: (a, ()) -> a;              unitR  = fst
unitR' :: a -> (a, ());              unitR' = (,())
assocR :: ((a,b),c) -> (a,(b,c));    assocR ((a,b),c) = (a,(b,c))
assocL :: (a,(b,c)) -> ((a,b),c);    assocL (a,(b,c)) = ((a,b),c)

-- Coproduct
counitL  :: Either Void a -> a;              counitL  = either absurd id
counitL' :: a -> Either Void a;              counitL' = Right
counitR  :: Either a Void -> a;              counitR  = either id absurd
counitR' :: a -> Either a Void;              counitR' = Left
coassocR :: Either (Either a b) c -> Either a (Either b c)
coassocR = either (second Left) (Right . Right)
coassocL :: Either a (Either b c) -> Either (Either a b) c
coassocL = either (Left . Left) (first Right)
```

---

## I. `Cartesian` Laws

### 1. Left unit

```
dimap unitL' unitL (proUnit *** p)  =  p
```

`proUnit *** p :: p ((),a) ((),b)`.  Pre-composing with `unitL' = ((),)` and
post-composing with `unitL = snd` recovers `p`.

### 2. Right unit

```
dimap unitR' unitR (p *** proUnit)  =  p
```

`p *** proUnit :: p (a,()) (b,())`.  Pre-compose with `unitR' = (,())` and
post-compose with `unitR = fst`.

### 3. Associativity

```
dimap assocL assocR ((p *** q) *** r)  =  p *** (q *** r)
```

`(p *** q) *** r :: p ((a,a'),a'') ((b,b'),b'')`.  Re-bracketing with
`assocL`/`assocR` gives `p *** (q *** r) :: p (a,(a',a'')) (b,(b',b''))`.

### 4. Naturality (compatibility with `dimap`)

```
dimap f g p  ***  dimap h k q  =  dimap (bimap f h) (bimap g k) (p *** q)
```

This expresses that `(***)` is a natural transformation; it likely follows from
the above three laws together with parametricity, but can be stated explicitly
as a sanity check on instances that have multiple implementations of `(***)`.

### Discussion

The three laws (left unit, right unit, associativity) are exactly the coherence
conditions for a **lax monoidal functor** from `(Hask × Hask^op, (,), ((),()))`
to `(Set, ×, 1)`. They are the profunctorial analogue of the `Applicative` laws,
as made precise by the isomorphism

```
Cartesian p  ≅  forall x. Applicative (p x)
```

(exposed in the module as `pureDefault` / `liftA2Default`).

**Should `(***)` be symmetric?**  That is, should we require

```
dimap swap swap (p *** q)  =  q *** p
```

where `swap (x,y) = (y,x)`?  This holds for `(->)` and most instances.
However, it is **not** imposed here, because:

- Ordered products arise naturally in practice: `TreeRep` treats `(a, (b, c))`
  and `(c, (b, a))` as distinct representations.
- `Clown f` (for `Divisible f`) has `p1 *** p2 = divided p1 p2`, and
  `divided` may be sensitive to order.
- Requiring symmetry would rule out useful instances.

---

## II. `Cocartesian` Laws

Dual to `Cartesian`:

### 1. Left unit (counit on left)

```
dimap counitL counitL' (proEmpty +++ p)  =  p
```

`proEmpty +++ p :: p (Either Void a) (Either Void b)`.  Counit isomorphism on
both sides gives back `p`.

### 2. Right unit (counit on right)

```
dimap counitR counitR' (p +++ proEmpty)  =  p
```

### 3. Associativity

```
dimap coassocL coassocR ((p +++ q) +++ r)  =  p +++ (q +++ r)
```

### 4. Naturality

```
dimap f g p  +++  dimap h k q  =  dimap (bimap f h) (bimap g k) (p +++ q)
```

### Discussion

These are the coherence conditions for a lax monoidal functor with respect to
`Either`, i.e., the profunctorial analogue of `Alternative`/`Decidable`.

**Should `(+++)` be symmetric?**  Same arguments as for `(***)`: not required,
and `Clown (Decidable f)` is a natural counterexample since `chosen` is
order-sensitive.

---

## III. Distributivity Laws (when both `Cartesian` and `Cocartesian`)

When `p` is both `Cartesian` and `Cocartesian`, the two monoidal structures
interact. There are two natural distributivity laws; they are **not symmetric**.

Define the four structural maps:

```haskell
distR   :: (Either a a', b) -> Either (a,b) (a',b)
distR (ea, b) = bimap (,b) (,b) ea

undistR :: Either (a,b) (a',b) -> (Either a a', b)
undistR = either (first Left) (first Right)

distL   :: (a, Either b b') -> Either (a,b) (a,b')
distL (a, eb) = bimap (a,) (a,) eb

undistL :: Either (a,b) (a,b') -> (a, Either b b')
undistL = either (second Left) (second Right)
```

### Right distributivity

```
dimap distR undistR ((p +++ q) *** r)  =  (p *** r) +++ (q *** r)
```

In a near-semiring, this is `(x + y) * z = (x * z) + (y * z)`.

This law is used centrally in `FreeCocartesian`'s `Cartesian` instance (see
`multF`), but it **does not hold for all instances**.

Counterexamples:

- **`Joker IO`**: for `Joker f` the law reduces to
  `liftA2 f (x <|> y) z  =  liftA2 f x z <|> liftA2 f y z`,
  i.e., `<*>` distributes from the left over `<|>`.  For `IO` (with
  exception-based `<|>`), the right operand `z` is sequenced after the sum
  part; on the RHS `z` may be executed in *both* branches before the `<|>`
  selects one, so the two sides can diverge on effects.

- **`ArrowChoice a`** (viewed as `Cartesian`/`Cocartesian`): `(***)` is
  defined as `first p >>> second q` and `(+++)` as `left p >>> right q`,
  using `Category` composition `>>>`.  On the LHS the sum `p +++ q` is formed
  first and then paired with `r`; on the RHS `r` is paired independently
  inside each branch.  The two sides sequence effects in different orders and
  are not equal in general.

Note: `Joker []` and `Joker (Either e)` (with the standard `Alternative`
instances) *do* satisfy right distributivity, because `<*>` for lists and
`Either` distributes cleanly over `<|>` from the left.

### Left distributivity

```
dimap distL undistL (p *** (q +++ r))  =  (p *** q) +++ (p *** r)
```

In a near-semiring, this would be `x * (y + z) = (x * y) + (x * z)`.

This law **does not hold in general**.  The canonical counterexample is
`Joker []`, because `<*>` for lists does not distribute from the right over
`<|>`:

```haskell
let x = [id, id]; y = [1]; z = [2]
x <*> (y <|> z)         -- [1,2,1,2]
(x <*> y) <|> (x <*> z) -- [1,1,2,2]
```

`ArrowChoice` similarly fails left distributivity.

### Recommendation

**Neither distributivity law holds universally.**  The `TreeRep` near-semiring
model was originally motivated by right distributivity holding, but the
`ArrowChoice` and `IO` counterexamples show this was too optimistic.

The practical consequence is:

- `FreeCocartesian`'s `Cartesian` instance (`multF`) actually uses **both**
  left and right distributivity internally: it repeatedly expands
  `p *** (q +++ r)` into `(p *** q) +++ (p *** r)` (left) and
  `(p +++ q) *** r` into `(p *** r) +++ (q *** r)` (right), producing a
  flat formal sum of products — a polynomial normal form.  Feeding this
  back into an outer `p` via `foldFree` is only semantically correct if the
  outer `p`'s `(+++)` is commutative (so the order of the expanded terms does
  not matter).  `FreeCocartesian` is therefore best suited to interpreting into
  profunctors with symmetric `(+++)`.
- Both distributivity laws are best treated as **optional, stronger
  conditions** that some instances satisfy and others do not, rather than
  universal laws of `Cartesian`/`Cocartesian`.

---

## IV. Absorption Laws (when both `Cartesian` and `Cocartesian`)

In a near-semiring, `0 * x = 0`. In a semiring, `x * 0 = 0` additionaly. The profunctor analogues:

### Left absorption

```
proEmpty *** p  =  dimap fst absurd proEmpty
```

`proEmpty *** p :: p (Void, a) (Void, b)`.  The right-hand side
`dimap fst absurd proEmpty` re-tags the input/output with `fst` and `absurd`.
The law says the product must collapse to `proEmpty` whenever the left factor
has an uninhabited domain.

### Right absorption

```
p *** proEmpty  =  dimap snd absurd proEmpty
```

`p *** proEmpty :: p (a, Void) (b, Void)`.  Here `snd :: (a, Void) -> Void` and
`absurd :: Void -> (b, Void)`.

### Discussion

These are **genuine constraints**, not vacuously true.  Although no value of
type `Void` can arrive at runtime, a general profunctor `p` is not a function
type, so `p Void b` can be any type (e.g. for a constant profunctor `p _ _ = C`
it equals `C`, which may have many elements).  The law imposes a real condition:
the instance's `(***)` must route `Void`-bearing inputs through `proEmpty` rather
than producing some unrelated element of `p Void b`.

For `(->)` the laws hold because `Void -> b` is indeed a singleton (`absurd` is
the only inhabitant), so equality is forced.  For `Star f`, the laws hold because
`f` can never be invoked on an uninhabited type, giving `pure absurd` in both
cases.  For `Joker f`, left absorption requires `liftA2 (,) empty fa = empty`,
which is an `Alternative` law; so it holds for law-abiding `Alternative`
instances.

Whether to **formally impose** absorption laws is an open question.  They hold
for all current instances, but verifying them requires reasoning about the
`(***)` implementation rather than the type alone.

Note that `proUnit` is **not** a zero for `(***)` or `(+++)`: it is only the
multiplicative unit.  `proUnit +++ proUnit :: p (Either a a') (Either () ())`
is unrelated to `proUnit :: p a ()`, and there is no law connecting them.

---

## V. Summary and Recommendations

| Law | Status | Rationale |
|-----|--------|-----------|
| `Cartesian` left/right unit | **Required** | Monoidal coherence |
| `Cartesian` associativity | **Required** | Monoidal coherence |
| `Cocartesian` left/right unit | **Required** | Monoidal coherence |
| `Cocartesian` associativity | **Required** | Monoidal coherence |
| `Cartesian` commutativity (`swap`) | **Not required** | Breaks `TreeRep`, ordered instances |
| `Cocartesian` commutativity (`swap`) | **Not required** | Same reasons |
| Right distributivity of `(***)` over `(+++)` | **Optional** | Fails for `Joker IO`, `ArrowChoice`; required by `FreeCocartesian` |
| Left distributivity of `(***)` over `(+++)` | **Optional** | Fails for `Joker []`, `ArrowChoice` |
| Absorption (`proEmpty *** p = ...`) | **Guideline only** | It is an independent condition (Absorption-only breakage is possible) actually, but all current instances satisfy. Most of the common usage will not violate. |

---

## VI. Relation to Existing Type Classes

| Type class | Relation |
|------------|----------|
| `Arrow` | Every `Arrow` gives a `Cartesian` (via `arr` + `***`) |
| `ArrowChoice` | Every `ArrowChoice` gives a `Cocartesian` (via `arr` + `+++`) |
| `Applicative f` | `Star f` is `Cartesian` iff `f` is `Applicative` |
| `Functor f` | `Star f` is `Cocartesian` iff `f` is a `Functor` |
| `Divisible f` | `Clown f` is `Cartesian` iff `f` is `Divisible` |
| `Decidable f` | `Clown f` is `Cocartesian` iff `f` is `Decidable` |

The `Cartesian` laws, viewed through the `Applicative` isomorphism, correspond
exactly to the `Applicative` laws (`pure`/`<*>`).  Any `Applicative` instance
that satisfies the standard `Applicative` laws automatically gives a `Cartesian`
instance satisfying the laws above.

---

## VII. Open Questions

1. **Should distributivity be captured as a separate class?**
   Since neither distributivity law holds universally, one option is a separate
   class (e.g. `RightDistributive p`) for instances that do satisfy it,
   allowing `FreeCocartesian`'s `Cartesian` instance to require it as a
   constraint.

2. **A free `Bicartesian` for the commutative/symmetric case.**
   `FreeCocartesian p` carries an ordered sum, but its `Cartesian` instance
   (via `multF`) performs a full polynomial expansion using *both*
   distributivities and implicitly relies on the target `p` having commutative
   `(+++)` for the result to be meaningful.  A separate construction — call it
   `FreeX p` for now — should be introduced that:
   - represents formal sums as a *multiset* (or sorted structure) of products,
     making `(+++)` commutative by construction;
   - has full left+right distributivity and both absorption laws built in;
   - corresponds to a free semiring generated by a `Cartesian p`.
   This would be the correct home for `ptraverseDay` (currently in
   `Data.PTraversable.Internal.Day`), which uses `FreeCocartesian Mono` but
   only because the order of monomials happens not to matter for the final
   fold.

3. **`PTraversable` laws**: what equations should `ptraverse` satisfy?
   Specialising `ptraverse` to `p = Star f` recovers `traverse`, so the laws
   should generalise the standard `Traversable` laws.  Candidate laws:

   - **Functoriality** (`p = (->`)):
     ```
     ptraverse (h :: a -> b)  =  fmap h
     ```
     i.e., `ptraverse` restricted to `(->)` is `fmap`.  This corresponds to
     the `Identity` law of `Traversable`
     (`traverse (Identity . f) = Identity . fmap f`).

   - **Composition** (`Procompose`):
     ```
     ptraverse (Procompose p q)  =  Procompose (ptraverse p) (ptraverse q)
     ```
     `ptraverse` distributes over profunctor composition, lifting the
     intermediate type as well.  This corresponds to the `Compose` law
     (`traverse (Compose . fmap g . f) = Compose . fmap (traverse g) . traverse f`).

   Whether these two candidates are sufficient, or whether further coherence
   conditions with `(***)` and `(+++)` are needed, is an open question.

4. **Commutativity for `Forget r`**: `Forget r` satisfies commutativity whenever
   `r` is a commutative `Monoid`.
   Should there be a subclass `CommutativeCartesian` for the symmetric case?

5. **Intensional vs. propositional equality**: all laws above are stated as
   equalities of Haskell values.  For types involving `Void` or degenerate
   cases, these hold trivially by parametricity.  The interesting cases are
   where the types are inhabited.
