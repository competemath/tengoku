module

public import Tengoku.Seed.Data.Set.Prod
public import Tengoku.Seed.Data.Finset.Piecewise
public import Tengoku.Seed.Data.Fintype.Basic
public import Tengoku.Seed.Data.Set.Finite.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rectangularity and independent local contracts

The binary result is the standard communication-complexity characterization:
a relation is a Cartesian rectangle exactly when it is closed under exchanging
coordinates.  The indexed results characterize the corresponding full-product
property.

The binary theorem is the folklore result used throughout communication
complexity (for example, Kushilevitz and Nisan, *Communication Complexity*,
1997).  It is also the empty-determinant special case of Fagin's lossless-join
characterization of multivalued dependencies (ACM TODS, 1977).

## Two indexed characterizations, and why both are here

`coordinate_product_iff_recombination_closed` is close to definitional: one
inclusion of the product equality always holds, so the statement reduces to
unfolding `Set.pi` against the recombination hypothesis.  It is kept as a
helper, not as a headline result.

`coordinate_product_iff_spliceClosed` is the substantive statement.  Splice
closure is a *local* condition: update one accepted point at a single
coordinate using another accepted point's value there.  Over a finite index and
a nonempty predicate it is equivalent to being the full product, by splicing
coordinates one at a time along a `Finset.piecewise` induction.

Finiteness is necessary, not an artifact of the proof.
`spliceClosed_finitelySupported` and `not_isCoordinateProduct_finitelySupported`
exhibit the counterexample: over `ℕ`, the Boolean functions with finite support
are splice closed and have full unary projections, yet the constantly-true
function is missing, so they are not the full product.

No claim is made here about hyperproperties.  These predicates describe one
state or trace at a time; relational properties of several executions require
the lifting in `Hyperproperties`.
-/

namespace AISafetyAtlas.Compositional

/-- A binary relation is a Cartesian product of its two projections.-/
@[expose] public def IsRectangle {X Y : Type*} (R : Set (X × Y)) : Prop :=
  R = (Prod.fst '' R) ×ˢ (Prod.snd '' R)

/-- Coordinate exchange: two accepted pairs may exchange their second
coordinates.  The other mixed pair follows by exchanging the arguments.-/
@[expose] public def ExchangeClosed {X Y : Type*} (R : Set (X × Y)) : Prop :=
  ∀ p ∈ R, ∀ q ∈ R, (p.1, q.2) ∈ R

/-- The values occurring in coordinate `i` among the accepted global states.-/
@[expose] public def coordinateProjection {ι : Type*} {X : ι → Type*}
    (P : Set (∀ i, X i)) (i : ι) : Set (X i) :=
  Function.eval i '' P

/-- An indexed predicate is the full product of its unary projections.-/
@[expose] public def IsCoordinateProduct {ι : Type*} {X : ι → Type*}
    (P : Set (∀ i, X i)) : Prop :=
  P = Set.pi Set.univ (coordinateProjection P)

/-- Every point assembled from coordinate values that occur locally is
accepted globally.  This is arbitrary (possibly infinite) recombination, not
merely closure under finitely many single-coordinate updates.-/
@[expose] public def RecombinationClosed {ι : Type*} {X : ι → Type*}
    (P : Set (∀ i, X i)) : Prop :=
  ∀ x, (∀ i, x i ∈ coordinateProjection P i) → x ∈ P

/-!
## Local splicing

Splice closure updates one accepted point at a *single* coordinate, using the
value another accepted point takes there.  Unlike `RecombinationClosed` it never
rebuilds a point from scratch, so it is a genuinely local condition.
-/

/-- Closure under updating one accepted point at a single coordinate with the
value another accepted point takes at that coordinate.-/
@[expose] public def SpliceClosed {ι : Type*} [DecidableEq ι] {X : ι → Type*}
    (P : Set (∀ i, X i)) : Prop :=
  ∀ x ∈ P, ∀ y ∈ P, ∀ i, Function.update x i (y i) ∈ P

/-!
### The binary theorem is the two-coordinate case

`ExchangeClosed` replaces the second coordinate of an accepted pair by the
second coordinate of another accepted pair, which is exactly a splice at that
coordinate.  Applying it with the arguments swapped splices the first
coordinate, so both single-coordinate updates are available.
-/

/-!
## Necessity of finiteness

Over an infinite index the finite-support Boolean functions are splice closed
and have full unary projections, but omit the constantly-true function.
-/

/-- Boolean sequences with finitely many `true` values.-/
@[expose] public def FinitelySupported : Set (ℕ → Bool) :=
  {x | {n | x n = true}.Finite}

end AISafetyAtlas.Compositional
