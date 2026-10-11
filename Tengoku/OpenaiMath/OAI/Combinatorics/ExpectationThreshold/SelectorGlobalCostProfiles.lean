import Tengoku.OpenaiMath.OAI.Combinatorics.ExpectationThreshold.SelectorDefinitions
import Tengoku.OpenaiMath.OAI.Combinatorics.ExpectationThreshold.SelectorCountingWordsProducts
import Tengoku.OpenaiMath.OAI.Combinatorics.ExpectationThreshold.TupleGeometric

namespace OAI

/-!
# Summing the full-profile weights

The reconstruction sets may depend on the entire profile. Once their counting
bound has been replaced by the uniform entropy bound, the remaining full
profiles can be grouped by row counts. The literal word-count weights have
total mass at most one within each such group.
-/

open scoped BigOperators

namespace TalagrandThreshold.Selector

end TalagrandThreshold.Selector

end OAI
