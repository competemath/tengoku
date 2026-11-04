import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.RepeatedPairVariation
import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.SmallSampleScalar
import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.CandidateVectors

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Actual second-variation exclusion of heavy candidates for sample sizes one and two. -/
namespace EntropyConstrainedMissingMass
noncomputable section

def repeatedPairHessian (t : ℕ) (q z : ℝ) : ℝ :=
  weightedCurvature t q + (deriv (missingMassTerm t) q - deriv (missingMassTerm t) z) /
    (Real.log z - Real.log q)

namespace ProbabilityVector

end ProbabilityVector
end
end EntropyConstrainedMissingMass
