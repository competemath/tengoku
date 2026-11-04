import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.Probability
import Tengoku.Seed.Topology.Semicontinuity.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Lower semicontinuity of extended entropy and closedness of entropy constraints. -/

namespace EntropyConstrainedMissingMass.ProbabilityVector
variable {ι : Type*}

/--
@isnad1 id=continuo.0h2v.s4.ee42f01fb220 from=translated src=- shape=447d4033 vocab=8a201739
-/
theorem continuous_coord (i : ι) : Continuous (fun p : ProbabilityVector ι => p.coord i) :=
  ((lp.evalCLM ℝ (fun _ : ι => ℝ) 1 i).continuous).comp continuous_subtype_val

/-- Entropy is lower semicontinuous even in the coordinatewise topology on all real vectors.
@isnad1 id=lowersem.0h1v.s5.a69f2f5e8325 from=translated src=- shape=cf13ac30 vocab=d3a40ada
-/
theorem lowerSemicontinuous_entropy_function :
    LowerSemicontinuous (fun p : ι → ℝ => ∑' i, ENNReal.ofReal (Real.negMulLog (p i))) := by
  apply lowerSemicontinuous_tsum
  intro i
  exact (ENNReal.continuous_ofReal.comp
    (Real.continuous_negMulLog.comp (continuous_apply i))).lowerSemicontinuous

/-- In particular extended entropy is lower semicontinuous in the manuscript's ℓ¹ topology.
@isnad1 id=lowersem.0h1v.s4.73fbd93a3ccc from=translated src=- shape=224be8a6 vocab=37bb9b40
-/
theorem lowerSemicontinuous_entropy :
    LowerSemicontinuous (fun p : ProbabilityVector ι => p.entropy) := by
  apply lowerSemicontinuous_tsum
  intro i
  exact (ENNReal.continuous_ofReal.comp
    (Real.continuous_negMulLog.comp (continuous_coord i))).lowerSemicontinuous

/--
@isnad1 id=isclosed.0h2v.s4.97a08e82d66d from=translated src=- shape=8bc8fdbb vocab=443159ea
-/
theorem isClosed_feasible (h : ℝ) : IsClosed (Feasible h : Set (ProbabilityVector ι)) :=
  lowerSemicontinuous_entropy.isClosed_preimage (ENNReal.ofReal h)

end EntropyConstrainedMissingMass.ProbabilityVector
