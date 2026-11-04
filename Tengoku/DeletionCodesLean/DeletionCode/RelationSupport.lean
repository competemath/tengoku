import Tengoku.DeletionCodesLean.DeletionCode.WitnessAlgebra

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms support_inclusion` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms isolated_coordinate_nonzero` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Support consequences of an actual rational relation between integer rule
vectors. In particular, a coordinate belonging to just one participating rule
cannot disappear when that rule's coefficient is nonzero.
-/
namespace DeletionCode.RelationSupport

open SignedSupport
open scoped BigOperators

/-- A coordinatewise rational relation on the actual integer spectrum vectors.-/
def Relation {I : Type*} [Fintype I] {L : ℕ}
    (G : I → Gram L → ℤ) (w : Gram L → ℤ) (a : I → ℚ) : Prop :=
  ∀ g, (w g : ℚ) = ∑ i, a i * (G i g : ℚ)

/--
@isnad1 id=ex.2h6v.s5.b677459090d1 from=translated src=- shape=e695ee8e vocab=c907ab2d
-/
theorem support_inclusion {I : Type*} [Fintype I] {L : ℕ}
    (G : I → Gram L → ℤ) (w : Gram L → ℤ) (a : I → ℚ)
    (hrel : Relation G w a) (g : Gram L) (hw : w g ≠ 0) :
    ∃ i, G i g ≠ 0 := by
  classical
  by_contra hnone
  push Not at hnone
  have hz : (w g : ℚ) = 0 := by
    rw [hrel g]
    apply Finset.sum_eq_zero
    intro i _
    simp [hnone i]
  exact hw (by exact_mod_cast hz)

/--
@isnad1 id=ne.4h7v.s6.38e9eb0ca2c6 from=translated src=- shape=2101f369 vocab=c907ab2d
-/
theorem isolated_coordinate_nonzero {I : Type*} [Fintype I] {L : ℕ}
    (G : I → Gram L → ℤ) (w : Gram L → ℤ) (a : I → ℚ)
    (hrel : Relation G w a) (i : I) (g : Gram L)
    (ha : a i ≠ 0) (hgi : G i g ≠ 0)
    (hother : ∀ j, j ≠ i → G j g = 0) : w g ≠ 0 := by
  classical
  have heq : (w g : ℚ) = a i * (G i g : ℚ) := by
    rw [hrel g]
    apply Finset.sum_eq_single i
    · intro j _ hji
      simp [hother j hji]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  intro hz
  have hcast : (G i g : ℚ) ≠ 0 := by exact_mod_cast hgi
  have hne := mul_ne_zero ha hcast
  apply hne
  simpa only [hz, Int.cast_zero] using heq.symm

end DeletionCode.RelationSupport
