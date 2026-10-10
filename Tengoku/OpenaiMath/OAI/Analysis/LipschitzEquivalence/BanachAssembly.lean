import Tengoku.OpenaiMath.OAI.Analysis.LipschitzEquivalence.SlotBudget

namespace OAI

universe uE uX uY

noncomputable section

namespace LipschitzCounterexample

namespace Criterion
open WeakSequences
open scoped NNReal

theorem contains_of_isometry_equiv {E : Type uE} {X : Type uX} {Y : Type uY} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (j : E →ₗᵢ[ℝ] X) (e : X ≃L[ℝ] Y) : ContainsLinearCopy E Y := by
  refine ⟨e.toContinuousLinearMap.comp j.toContinuousLinearMap, 1/(‖e.symm.toContinuousLinearMap‖+1),
    by positivity, ?_⟩
  intro z
  have he := e.symm.toContinuousLinearMap.le_opNorm (e (j z))
  change ‖e.symm (e (j z))‖ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e (j z)‖ at he
  simp only [e.symm_apply_apply, j.norm_map] at he
  change 1/(‖e.symm.toContinuousLinearMap‖+1)*‖z‖ ≤ ‖e (j z)‖
  rw [one_div_mul_eq_div]
  apply (div_le_iff₀ (by positivity : 0 < ‖e.symm.toContinuousLinearMap‖+1)).2
  nlinarith [norm_nonneg (e (j z))]

end Criterion
end LipschitzCounterexample

end

end OAI
