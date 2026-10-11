import Tengoku.OpenaiMath.OAI.Analysis.Daugavet.Stages

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

namespace ExactModuli.KW

lemma stageError_tendsto : Tendsto stageError atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)).mul_const (1/2:ℝ)
  change Tendsto (fun n : ℕ => (1/2:ℝ)^(n+1)) atTop (𝓝 0)
  simpa only [zero_mul, pow_succ] using h

lemma stageError_eventually_small {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, stageError n < ε :=
  eventually_atTop.mp (stageError_tendsto.eventually_lt_const hε)

end ExactModuli.KW

end

end OAI
