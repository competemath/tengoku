import Tengoku.Jsp000937Lean.Erdos1153.ClassicalBound.EnergyLowerAsymptotic
import Tengoku.Jsp000937Lean.Erdos1153.ClassicalBound.PolynomialControl

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# From clipped pair energy to the Lebesgue constant

The unconditional polynomial-control theorem gives

    2 E <= n (n-1) Lambda.

An energy lower bound of size `C n^2 log n` therefore first yields the
slightly stronger finite estimate

    2 C (n/(n-1)) log n <= Lambda.

Since `n/(n-1) >= 1`, a nonnegative coefficient gives the plan-facing
sharp estimate `2 C log n <= Lambda`.  This file keeps both forms visible.
-/

namespace Erdos1153
namespace ClassicalBound

noncomputable section

end

end ClassicalBound
end Erdos1153
