import Tengoku.LeanCommutator.PavingSeparation.Paving

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Lower bounds for arbitrary original-coordinate partitions -/

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator

namespace PavingSeparation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Some color class is at least as large as the real-valued average.
@isnad1 id=ex.0h3v.s5.6efdd0c81181 from=translated src=- shape=15c4128f vocab=54dd3e43
-/
theorem exists_colorClass_card_ge_average (r : ℕ) [NeZero r] (c : ι → Fin r) :
    ∃ a : Fin r, (Fintype.card ι : ℝ) / r ≤ ((colorClass c a).card : ℝ) := by
  have hr : (r : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne r
  have heq : (r : ℝ) * ((Fintype.card ι : ℝ) / r) = Fintype.card ι := by
    field_simp
  have hb : Fintype.card (Fin r) • ((Fintype.card ι : ℝ) / r) ≤
      (Fintype.card ι : ℝ) := by
    simpa only [Fintype.card_fin, nsmul_eq_mul, heq] using le_refl (Fintype.card ι : ℝ)
  obtain ⟨a, ha⟩ := Fintype.exists_le_card_fiber_of_nsmul_le_card c hb
  exact ⟨a, ha⟩

end PavingSeparation
