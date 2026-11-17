import Tengoku.PaperCLean.PaperCV282.ScalarSteinInput
import Tengoku.Seed.Analysis.Complex.ExponentialBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Exact exponential tail for a Poisson-size cloud -/
namespace PaperC.Prel8.PoissonCloudTail
open V282.ScalarSteinInput Filter Topology
open scoped NNReal
noncomputable section

def tail (rate : ℝ≥0) (K : ℕ) : ℝ := ∑' k : ℕ, if K<k then poissonMass rate k else 0

/-- The genuine upper-tail series is summable.
@isnad1 id=summable.0h2v.s5.4cf6128bc93c from=translated src=- shape=aa83dcf1 vocab=f00ab7b8
-/
theorem tail_summable (rate : ℝ≥0) (K : ℕ) :
    Summable (fun k : ℕ ↦ if K<k then poissonMass rate k else 0) := by
  apply (hasSum_poissonMass rate).summable.of_nonneg_of_le
  · intro k; split_ifs <;> first | exact poissonMass_nonneg rate k | exact le_rfl
  · intro k; split_ifs <;> first | exact le_rfl | exact poissonMass_nonneg rate k

/-- This tail vanishes precisely in the growing-intensity regime used in Appendix F/G.
@isnad1 id=tendsto.1h1v.s6.7d224adb4fd7 from=translated src=- shape=93b26045 vocab=6f5f7060
-/
theorem doubled_rate_tendsto {rate : ℕ → ℝ≥0}
    (hr : Tendsto (fun M ↦ (rate M:ℝ)) atTop atTop) :
    Tendsto (fun M ↦ Real.exp (-((2*Real.log 2-1)*(rate M:ℝ)))) atTop (𝓝 0) := by
  have hc : -(2*Real.log 2-1)<0 := by nlinarith [Real.log_two_gt_d9]
  simpa only [Function.comp_def,neg_mul] using Real.tendsto_exp_atBot.comp (hr.const_mul_atTop_of_neg hc)

end
end PaperC.Prel8.PoissonCloudTail
