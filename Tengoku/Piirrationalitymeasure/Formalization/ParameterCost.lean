import Tengoku.Piirrationalitymeasure.Formalization.ParameterSavingSeries
import Tengoku.Piirrationalitymeasure.Formalization.ParameterSavingContinuity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Continuity of the arithmetic cost and positivity near the selected parameters. -/

namespace PiIrrationality

open Filter Set
open scoped Topology

theorem continuous_parameterSmoothCost : Continuous parameterSmoothCost := by
  unfold parameterSmoothCost
  fun_prop

theorem continuousAt_parameterCost {p : ℝ × ℝ} (hp : Admissible p) :
    ContinuousAt parameterCost p := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  exact continuous_parameterSmoothCost.continuousAt.sub
    (continuousAt_savingPhi (by linarith) (by linarith) (by linarith))

theorem parameterCost_continuousOn : ContinuousOn parameterCost {p | Admissible p} :=
  fun _ hp => (continuousAt_parameterCost hp).continuousWithinAt

theorem savingPhi_pos_near_candidate : ∀ᶠ p in 𝓝 candidate, 0 < savingPhi p := by
  have hc : ContinuousAt savingPhi candidate := by
    apply continuousAt_savingPhi <;> norm_num [candidate]
  exact hc.eventually_const_lt savingPhi_candidate_pos

end PiIrrationality
