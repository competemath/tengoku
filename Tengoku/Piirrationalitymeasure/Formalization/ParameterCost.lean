import Tengoku.Piirrationalitymeasure.Formalization.ParameterSavingSeries
import Tengoku.Piirrationalitymeasure.Formalization.ParameterSavingContinuity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Continuity of the arithmetic cost and positivity near the selected parameters. -/

namespace PiIrrationality

open Filter Set
open scoped Topology

/--
@isnad1 id=continuo.0h0v.s4.378f813e0bfb from=translated src=- shape=8e22ceaf vocab=65dfcf18
-/
theorem continuous_parameterSmoothCost : Continuous parameterSmoothCost := by
  unfold parameterSmoothCost
  fun_prop

/--
@isnad1 id=continuo.1h1v.s5.af903805316d from=translated src=- shape=b48b8bd5 vocab=cee44cec
-/
theorem continuousAt_parameterCost {p : ℝ × ℝ} (hp : Admissible p) :
    ContinuousAt parameterCost p := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  exact continuous_parameterSmoothCost.continuousAt.sub
    (continuousAt_savingPhi (by linarith) (by linarith) (by linarith))

/--
@isnad1 id=continuo.0h0v.s5.7de96430ea0a from=translated src=- shape=57ebd691 vocab=a349016a
-/
theorem parameterCost_continuousOn : ContinuousOn parameterCost {p | Admissible p} :=
  fun _ hp => (continuousAt_parameterCost hp).continuousWithinAt

/--
@isnad1 id=eventual.0h0v.s5.86158da5a074 from=translated src=- shape=32d43f48 vocab=3d3f8981
-/
theorem savingPhi_pos_near_candidate : ∀ᶠ p in 𝓝 candidate, 0 < savingPhi p := by
  have hc : ContinuousAt savingPhi candidate := by
    apply continuousAt_savingPhi <;> norm_num [candidate]
  exact hc.eventually_const_lt savingPhi_candidate_pos

end PiIrrationality
