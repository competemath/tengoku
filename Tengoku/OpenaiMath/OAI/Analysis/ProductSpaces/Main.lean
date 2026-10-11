import Tengoku.OpenaiMath.OAI.Analysis.ProductSpaces.ExponentialExcess

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace IndependentProducts

lemma exponentialLaw_hypotheses : MultiplierHypotheses exponentialLaw := by
  refine ⟨inferInstance, exponentialLaw_positive, ?_, exponentialLaw_mean, exponentialLaw_memLp⟩
  intro c hc
  have h1 : (1 : ℝ) = c := by
    calc
      1 = ∫ w : ℝ, w ∂exponentialLaw := exponentialLaw_mean.symm
      _ = ∫ _ : ℝ, c ∂exponentialLaw := integral_congr_ae hc
      _ = c := by simp
  have h2 : (∫ w : ℝ, w ^ 2 ∂exponentialLaw) = c ^ 2 := by
    calc
      _ = ∫ _ : ℝ, c ^ 2 ∂exponentialLaw :=
        integral_congr_ae (hc.mono fun w hw => congrArg (fun x : ℝ => x ^ 2) hw)
      _ = _ := by simp
  rw [exponentialLaw_second, ← h1] at h2
  norm_num at h2

end IndependentProducts

end

end OAI
