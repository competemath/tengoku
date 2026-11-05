module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.QWeylPullback
public import Tengoku.Seed.FieldTheory.IsAlgClosed.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-! The cubic witness parameters exist over every algebraically closed
characteristic-zero field. -/
namespace ChoppedPlane.QWeyl
variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]

/-- A nontrivial cube root of unity with its exact quadratic relation.
@isnad1 id=ex.0h1v.s7.a59a06349690 from=translated src=- shape=c835f6ce vocab=acc4cbe5
-/
theorem exists_cubic_parameter : ∃ q : K, q ^ 2 + q + 1 = 0 ∧ q ≠ 0 ∧ q ≠ 1 := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (-3 : K) (by decide : 0 < 2)
  have htwo : (2 : K) ≠ 0 := by norm_num
  have hq : ((w-1)/2)^2 + (w-1)/2 + 1 = 0 := by
    field_simp
    linear_combination hw
  refine ⟨(w-1)/2, hq, ?_, ?_⟩
  · intro h
    rw [h] at hq
    norm_num at hq
  · intro h
    rw [h] at hq
    norm_num at hq

end ChoppedPlane.QWeyl
