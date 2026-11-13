/-
# The commutator of a right pre-Lie ring is a Lie bracket

Mathlib's `Mathlib.Algebra.NonAssoc.PreLie.Basic` defines `RightPreLieRing` and
`RightPreLieAlgebra` and stops there. `Operad.TotalSpace` proved the Jacobi identity for the one
right pre-Lie ring it needed; the convolution algebra is a second, so the argument is stated here
once, for an arbitrary right pre-Lie ring.

The Lie structures are `def`s rather than instances. A ring that is associative is in particular
right pre-Lie, and mathlib already gives an associative ring its commutator Lie ring; a global
instance here would be a second path to the same structure. Each concrete right pre-Lie ring opts
in with a one-line instance.
-/
import Tengoku.Seed.Algebra.NonAssoc.PreLie.Basic
import Tengoku.Seed.Algebra.Lie.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe u v

namespace RightPreLieRing

variable {L : Type v} [RightPreLieRing L]

/-- The commutator `x * y - y * x`.-/
def commutator (x y : L) : L := x * y - y * x

/--
@isnad1 id=eq.0h3v.s6.ede0921ec79a from=translated src=- shape=ccde432c vocab=4fb59775
-/
lemma commutator_def (x y : L) : commutator x y = x * y - y * x := rfl

/--
@isnad1 id=eq.0h2v.s4.5e4111530756 from=translated src=- shape=acc2d0a4 vocab=fcf567da
-/
@[simp] lemma commutator_self (x : L) : commutator x x = 0 := sub_self _

/--
@isnad1 id=eq.0h3v.s5.83175da6dfc3 from=translated src=- shape=43748c76 vocab=5934cf4b
-/
lemma commutator_antisymm (x y : L) : commutator x y = -commutator y x := by
  simp only [commutator_def, neg_sub]

/--
@isnad1 id=eq.0h4v.s5.48b0b2c2f2aa from=translated src=- shape=b3d5c312 vocab=e2e1bdef
-/
lemma commutator_add_left (x x' y : L) :
    commutator (x + x') y = commutator x y + commutator x' y := by
  simp only [commutator_def, add_mul, mul_add]; abel

/--
@isnad1 id=eq.0h4v.s5.b4ece497a8cd from=translated src=- shape=f696fd59 vocab=e2e1bdef
-/
lemma commutator_add_right (x y y' : L) :
    commutator x (y + y') = commutator x y + commutator x y' := by
  simp only [commutator_def, add_mul, mul_add]; abel

/--
@isnad1 id=eq.0h3v.s5.b6856b200695 from=translated src=- shape=6f9dafc8 vocab=5934cf4b
-/
lemma commutator_neg_right (x y : L) : commutator x (-y) = -commutator x y := by
  simp only [commutator_def, mul_neg, neg_mul]; abel

/-- The cyclic sum of double commutators, written out in associators.-/
private lemma jacobi_aux (x y z : L) :
    commutator (commutator x y) z + commutator (commutator y z) x
        + commutator (commutator z x) y
      = (associator x y z - associator x z y) + (associator y z x - associator y x z)
        + (associator z x y - associator z y x) := by
  simp only [commutator_def, associator_apply, sub_mul, mul_sub]
  abel

/-- **The Jacobi identity**, in cyclic form. Each of the three differences of associators vanishes
by the right pre-Lie identity.
@isnad1 id=eq.0h4v.s6.466590e1dc3a from=translated src=- shape=bc929cf2 vocab=e2e1bdef
-/
theorem jacobi (x y z : L) :
    commutator (commutator x y) z + commutator (commutator y z) x
        + commutator (commutator z x) y = 0 := by
  rw [jacobi_aux, assoc_symm x y z, assoc_symm y z x, assoc_symm z x y]
  abel

/-- **A right pre-Lie ring is a Lie ring under its commutator.** Mathlib states the Jacobi
identity in Leibniz form, which follows from the cyclic form and antisymmetry.-/
@[reducible] def toLieRing : LieRing L where
  bracket := commutator
  add_lie x y z := commutator_add_left x y z
  lie_add x y z := commutator_add_right x y z
  lie_self x := commutator_self x
  leibniz_lie x y z := by
    show commutator x (commutator y z)
      = commutator (commutator x y) z + commutator y (commutator x z)
    have h := jacobi x y z
    have a1 : commutator (commutator y z) x = -commutator x (commutator y z) :=
      commutator_antisymm _ _
    have a2 : commutator (commutator z x) y = commutator y (commutator x z) := by
      rw [commutator_antisymm (commutator z x) y, commutator_antisymm z x,
        commutator_neg_right, neg_neg]
    have goal_eq : commutator x (commutator y z)
          - (commutator (commutator x y) z + commutator y (commutator x z))
        = -(commutator (commutator x y) z + commutator (commutator y z) x
            + commutator (commutator z x) y) := by
      rw [a1, a2]; abel
    rw [← sub_eq_zero, goal_eq, h, neg_zero]

/-- **A right pre-Lie algebra is a Lie algebra under its commutator.**-/
@[reducible] def toLieAlgebra (R : Type u) [CommRing R] [RightPreLieAlgebra R L] :
    letI := toLieRing (L := L); LieAlgebra R L :=
  letI := toLieRing (L := L)
  { (inferInstance : Module R L) with
    lie_smul := fun t x y => by
      show commutator x (t • y) = t • commutator x y
      rw [commutator_def, commutator_def, mul_smul_comm, smul_mul_assoc, smul_sub] }

end RightPreLieRing
