/-
# The signed total space, and the graded Jacobi identity

`Operad.GradedPreLie` proves the graded pre-Lie identity arity by arity, with explicit
reindexings. Reading off the Jacobi identity from it in that form would mean tracking twelve
products across six different arity expressions at once.

Bundling into a direct sum removes all of that: every product lands in the single type
`TotS R P`, the associator is mathlib's, and the twelve-term regrouping becomes one call to the
`module` tactic. This is the same move `Operad.TotalSpace` makes for the unsigned product; the
two cannot share a type, because a type carries only one multiplication, so `PieceS` is a second
synonym for `P (k + 1)` carrying the signed one.

Note what is *not* claimed. A graded Lie structure is not a `LieRing` on `TotS R P`: the sign
`(-1)^(j k)` depends on the degrees of the arguments, so the identity holds for homogeneous
elements and does not extend to the whole direct sum. The statements below are therefore about
`incS`-images, and the degrees appear explicitly.
-/
import Tengoku.LeanOperads.Operad.GradedPreLie
import Tengoku.LeanOperads.Operad.TotalSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe u v

namespace Operad

open NSOperad DirectSum

/-- The degree-`k` piece of the signed total space.-/
@[nolint unusedArguments]
def PieceS (R : Type u) [CommRing R] (P : ℕ → Type v) (k : ℕ) : Type v := P (k + 1)

section

variable {R : Type u} [CommRing R] {P : ℕ → Type v}
  [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)]

instance (k : ℕ) : AddCommGroup (PieceS R P k) := inferInstanceAs (AddCommGroup (P (k + 1)))

instance (k : ℕ) : Module R (PieceS R P k) := inferInstanceAs (Module R (P (k + 1)))

variable [NSOperad R P]

/-- The signed circle product as a graded multiplication.-/
instance : GradedMonoid.GMul (PieceS R P) where
  mul {_ _} a b := sstar (R := R) a b

instance : DirectSum.GNonUnitalNonAssocSemiring (PieceS R P) where
  mul_zero a := sstar_zero (R := R) a
  zero_mul b := zero_sstar (R := R) b
  mul_add a b c := sstar_add_right (R := R) a b c
  add_mul a b c := sstar_add_left (R := R) a b c

/-- The total space carrying the signed product.-/
@[nolint unusedArguments]
abbrev TotS (R : Type u) [CommRing R] (P : ℕ → Type v)
    [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P] : Type v :=
  ⨁ k : ℕ, PieceS R P k

/-- The inclusion of a homogeneous piece.-/
abbrev incS (k : ℕ) : PieceS R P k →+ TotS R P := DirectSum.of (PieceS R P) k

/--
@isnad1 id=eq.0h6v.s9.1d63e840a83d from=translated src=- shape=134cdc6e vocab=6022da66
-/
@[simp] lemma incS_mul_incS {i j : ℕ} (a : PieceS R P i) (b : PieceS R P j) :
    (incS i a * incS j b : TotS R P) = incS (i + j) (sstar (R := R) a b) :=
  DirectSum.of_mul_of a b

/-! ### `R`-bilinearity of the signed product on the total space -/

/-! ### The graded pre-Lie identity on the total space -/

/-! ### The graded Jacobi identity -/

/-- The graded bracket of two elements whose degrees are asserted to be `m` and `n`. Degrees are
parameters rather than being read off the elements, because an element of a direct sum need not
be homogeneous; every use below supplies the degree of an `incS`-image.-/
def brT (m n : ℕ) (x y : TotS R P) : TotS R P :=
  x * y - ((-1 : R) ^ (m * n)) • (y * x)

/-! ### Two equal odd arguments

Applying the graded pre-Lie identity with its last two arguments *equal and odd* gives only
`A(x, Θ, Θ) = -A(x, Θ, Θ)`, that is, `2 A(x, Θ, Θ) = 0` (`two_smul_associator_odd`). The
associator in fact vanishes over any commutative ring (`associator_self_one`): its disjoint-slot
terms cancel in pairs (`sstar_sstar_self_one`). -/

/-! ### The differential

For an odd `Θ` solving the Maurer–Cartan equation, `d = ⁅Θ, -⁆` squares to `-A(x, Θ, Θ)`, which
vanishes by `associator_self_one`. So `d² = 0` holds over any commutative ring. -/

end

end Operad
