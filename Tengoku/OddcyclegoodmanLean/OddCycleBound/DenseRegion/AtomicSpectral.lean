import Tengoku.Seed.Analysis.Normed.Operator.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace OddCycleBound.DenseRegion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/--
@isnad1 id=le.2h4v.s8.3328f137fe6d from=translated src=- shape=96676c59 vocab=dce545e8
-/
lemma abs_eigenvalue_le_opNorm (A : E →L[ℝ] E) {lam : ℝ} {v : E}
    (hv : v ≠ 0) (heigen : A v = lam • v) : |lam| ≤ ‖A‖ := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hmul : |lam| * ‖v‖ ≤ ‖A‖ * ‖v‖ := by
    calc
      |lam| * ‖v‖ = ‖lam • v‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = ‖A v‖ := congrArg norm heigen.symm
      _ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
  exact le_of_mul_le_mul_right hmul hvpos

/--
@isnad1 id=mem.3h4v.s8.4de7897193d7 from=translated src=- shape=5e1b80bd vocab=fd267087
-/
theorem eigenvalue_mem_halfInterval (A : E →L[ℝ] E) {lam : ℝ} {v : E}
    (hA : ‖A‖ ≤ (1 : ℝ) / 2) (hv : v ≠ 0) (heigen : A v = lam • v) :
    lam ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2) := by
  have habs : |lam| ≤ (1 : ℝ) / 2 := (abs_eigenvalue_le_opNorm A hv heigen).trans hA
  constructor <;> linarith [neg_abs_le lam, le_abs_self lam]

end OddCycleBound.DenseRegion
