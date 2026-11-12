/-
# The total space as a pre-Lie ring

`Operad.PreLie` proves the pre-Lie identity in *graded* form: `⋆` takes `P (j+1)` and `P (k+1)`
to `P (j+k+1)`, and `star_assoc_symm` is an identity between elements of a fixed arity. To land
on mathlib's `RightPreLieRing` the grading has to be bundled into a single object.

That object is `⨁ k, Piece R P k`, graded by **arity minus one**. Mathlib's graded-ring machinery
does most of the work: `DirectSum.GNonUnitalNonAssocSemiring` asks for exactly a graded
multiplication together with `mul_zero`, `zero_mul`, `mul_add` and `add_mul`, which are the four
bilinearity lemmas for `⋆`, and it produces the `NonUnitalNonAssocRing` structure that
`RightPreLieRing` extends.

`Piece` is a type synonym for `P (k + 1)` carrying `R` as a phantom parameter. Without it the
graded instances below would have `R` appearing nowhere in their conclusions, and Lean rejects
them for having no synthesization order.
-/
import Tengoku.LeanOperads.Operad.PreLie
import Tengoku.Seed.Algebra.DirectSum.Ring
import Tengoku.Seed.Algebra.DirectSum.Module
import Tengoku.Seed.Algebra.NonAssoc.PreLie.Basic
import Tengoku.Seed.Algebra.Ring.Associator
import Tengoku.Seed.Algebra.Lie.Basic
import Tengoku.LeanOperads.Operad.Endomorphism

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe u v

namespace Operad

open NSOperad DirectSum

/-- The degree-`k` piece of the total space: operations of arity `k + 1`. Arity `0` is excluded,
since it carries no degree and the deformation complex does not use it.-/
@[nolint unusedArguments]
def Piece (R : Type u) [CommRing R] (P : ℕ → Type v) (k : ℕ) : Type v := P (k + 1)

section

variable {R : Type u} [CommRing R] {P : ℕ → Type v}
  [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)]

instance (k : ℕ) : AddCommGroup (Piece R P k) := inferInstanceAs (AddCommGroup (P (k + 1)))

instance (k : ℕ) : Module R (Piece R P k) := inferInstanceAs (Module R (P (k + 1)))

variable [NSOperad R P]

/-- The circle product as a graded multiplication: degrees add.-/
instance : GradedMonoid.GMul (Piece R P) where
  mul {_ _} a b := star (R := R) a b

/-- The four bilinearity lemmas for `⋆` are exactly what a graded non-unital non-associative
semiring structure asks for.-/
instance : DirectSum.GNonUnitalNonAssocSemiring (Piece R P) where
  mul_zero a := star_zero (R := R) a
  zero_mul b := zero_star (R := R) b
  mul_add a b c := star_add_right (R := R) a b c
  add_mul a b c := star_add_left (R := R) a b c

/-- The total space of an operad, graded by arity minus one.-/
@[nolint unusedArguments]
abbrev Tot (R : Type u) [CommRing R] (P : ℕ → Type v)
    [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P] : Type v :=
  ⨁ k : ℕ, Piece R P k

/-- The inclusion of a homogeneous piece.-/
abbrev inc (k : ℕ) : Piece R P k →+ Tot R P := DirectSum.of (Piece R P) k

@[simp] lemma inc_mul_inc {i j : ℕ} (a : Piece R P i) (b : Piece R P j) :
    (inc i a * inc j b : Tot R P) = inc (i + j) (star (R := R) a b) :=
  DirectSum.of_mul_of a b

/-! ### The pre-Lie identity on the total space

The associator is additive in each argument, so it is enough to check the identity on
homogeneous elements, where it is `star_assoc_symm`. -/

/-! ### The commutator is a Lie bracket

Mathlib's pre-Lie file stops at the `Left`/`Right PreLieRing` classes and does not derive a Lie
structure, so the Jacobi identity is proved here. The cyclic sum of double commutators collapses
into six associators which cancel in pairs — each pair being one instance of `tot_assoc_symm`. -/

/-- The commutator of the circle product.-/
def comm (x y : Tot R P) : Tot R P := x * y - y * x

@[simp] lemma comm_self (x : Tot R P) : comm x x = 0 := sub_self _

/-- The commutator, packaged as mathlib's bracket.-/
instance : Bracket (Tot R P) (Tot R P) := ⟨comm⟩

/-! ### `R`-bilinearity, and the Lie algebra structure

Mathlib's graded-ring machinery only knows that the multiplication on `⨁` is *additive* in each
slot. `⋆` is `R`-bilinear, and that upgrades the Lie ring to a Lie algebra, but it has to be
transported to the direct sum by hand. -/

/-! ### The Gerstenhaber bracket

Specialising to the endomorphism operad gives Gerstenhaber's construction *without its signs*:
the circle product on `⨁ n, End V (n+1)` is his `∘` with every sign set to `1`, and the
commutator is a Lie bracket. The two agree in characteristic `2`. Gerstenhaber's bracket itself
carries the suspension signs; it is `brT` on `TotS R (End R V)` (`Operad.TotalSpaceS`). -/

/-- The unsigned Gerstenhaber Lie ring of a module: the total space of its endomorphism operad,
with the unsigned circle product. The signed bracket is `brT` on `TotS R (End R V)`.-/
abbrev Gerstenhaber (R : Type u) [CommRing R] (V : Type v) [AddCommGroup V] [Module R V] :
    Type v :=
  Tot R (End R V)

end

end Operad
