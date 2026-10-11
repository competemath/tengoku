import Tengoku.OpenaiMath.OAI.Combinatorics.ExpectationThreshold.SelectorCountingEncodingBound
import Tengoku.OpenaiMath.OAI.Combinatorics.ExpectationThreshold.SelectorCommonWitness
import Tengoku.OpenaiMath.OAI.Combinatorics.ExpectationThreshold.SelectorProfile
import Tengoku.OpenaiMath.OAI.Combinatorics.ExpectationThreshold.SelectorEntropy
import Tengoku.OpenaiMath.OAI.Combinatorics.ExpectationThreshold.ProbabilityLikelihood
import Tengoku.OpenaiMath.OAI.Combinatorics.ExpectationThreshold.ColorArithmetic
import Tengoku

namespace OAI

/-!
# The actual contribution of one full selector profile

The common heavy sets are obtained separately for each occurring profile.
The entropy estimate removes their sizes before profiles are summed, so no
uniform choice of heavy sets across distinct profiles is required.
-/

noncomputable section
open scoped BigOperators

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α]

end TalagrandThreshold.Selector

end

end OAI
