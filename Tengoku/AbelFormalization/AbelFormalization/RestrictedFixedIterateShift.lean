import Tengoku.AbelFormalization.AbelFormalization.FixedIterateShift
import Tengoku.AbelFormalization.AbelFormalization.RestrictedExpressionTower

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

open Set Function
open scoped ContDiff

namespace AbelFormalization

set_option autoImplicit false

/-- Apply the scalar fixed-iterate shift to an analytic bounded-coordinate
coefficient.-/
def restrictedFixedIterateShift {p : ℕ} (d : ℕ) (D : RestrictedBox p)
    (b : RestrictedBox.analyticNearClosedBoxSubalgebra D) :
    ℝ × RestrictedBoxSpace p → ℝ :=
  fun q => fixedIterateShift d q.1
    ((b : RestrictedBoxSpace p → ℝ) q.2)

end AbelFormalization
