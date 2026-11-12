import Tengoku.AbelFormalization.AbelFormalization.HermiteContour
import Tengoku.AbelFormalization.AbelFormalization.HermiteBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Uniform bounds for contour interpolation coefficients

A uniform bound on the coefficient kernel and a bound on the boundary values
of the interpolated function control every coefficient.  Multiplication by
the total-degree factorial gives the same conclusion for the manuscript's
factorial-normalized coefficients, uniformly at colliding nodes.
-/

noncomputable section

open Set Metric Polynomial

namespace AbelFormalization

variable {ι : Type*} [Fintype ι]

end AbelFormalization
