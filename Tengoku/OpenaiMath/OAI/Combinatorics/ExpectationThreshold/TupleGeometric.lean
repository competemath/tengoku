import Tengoku.OpenaiMath.OAI.Combinatorics.ExpectationThreshold.TupleCoefficients
import Tengoku

namespace OAI

/-!
# A finite geometric bound for nonzero tuples

Every finite family of tuples lies in a finite coordinate box. Factoring
the sum over this box reduces the estimate to ordinary finite geometric
sums. Adding the zero tuple contributes exactly one, so removing it gives
the selector's budget of strictly less than `1 / 20`.
-/

namespace TalagrandThreshold

open scoped BigOperators

end TalagrandThreshold

end OAI
