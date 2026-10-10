import Tengoku.OpenaiMath.OAI.Analysis.NumericalRange.Main

namespace OAI

/-! Intrinsic domains, optimal similarities and matrix-valued boundary representations. -/

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
namespace AdmissibleDomain
variable (D : AdmissibleDomain)
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

theorem complete_analytic_similarity_bound_nonneg
    {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m]
    {S A : Matrix n n ℂ} (hS : IsUnit S)
    (F : ℂ → Matrix m m ℂ) {b : ℝ} (hb : 0 ≤ b)
    (hF : ‖completeAnalyticEval (S*A*S⁻¹) F‖ ≤ b) :
    ‖completeAnalyticEval A F‖ ≤ (‖S‖ * ‖S⁻¹‖) * b := by
  let R := baseMatrixHom (m := m) S
  let R' := baseMatrixHom (m := m) S⁻¹
  have hi : S⁻¹*S=1 := Matrix.nonsing_inv_mul S ((Matrix.isUnit_iff_isUnit_det S).mp hS)
  have hR : R'*R=1 := by
    change baseMatrixHom (m := m) S⁻¹ * baseMatrixHom S=1
    rw [← map_mul, hi, map_one]
  have he : completeAnalyticEval A F = R'*completeAnalyticEval (S*A*S⁻¹) F*R := by
    rw [completeAnalyticEval_similarity hS]
    change completeAnalyticEval A F = R'*(R*completeAnalyticEval A F*R')*R
    calc
      _ = 1*completeAnalyticEval A F*1 := by simp
      _ = _ := by rw [← hR]; noncomm_ring
  rw [he]
  calc
    _ ≤ ‖R'‖ * ‖completeAnalyticEval (S*A*S⁻¹) F‖ * ‖R‖ :=
      (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ ‖S⁻¹‖ * b * ‖S‖ := mul_le_mul
      (mul_le_mul (baseMatrixHom_norm S⁻¹) hF (norm_nonneg _) (norm_nonneg _))
      (baseMatrixHom_norm S) (norm_nonneg _) (mul_nonneg (norm_nonneg _) hb)
    _ = _ := by ring

end AdmissibleDomain
end CompleteCrouzeix
end
end

end OAI
