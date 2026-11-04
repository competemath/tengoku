import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.HeavyInterpolation
import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.CertificateBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The real-exponent heavy-tail cutoff. -/

open Set
namespace EntropyConstrainedMissingMass
noncomputable section

private def cutoffAux (s z u : ℝ) : ℝ := realMissingMassDeriv s u -
  s*u*(Real.log z-Real.log u)*(1-u)^(s-1)

end
end EntropyConstrainedMissingMass
