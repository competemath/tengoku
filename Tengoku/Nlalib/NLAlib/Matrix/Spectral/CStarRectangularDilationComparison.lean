import Tengoku.Nlalib.NLAlib.Matrix.Spectral.CStarRectangularDilationPositive
import Tengoku.Nlalib.NLAlib.ForMathlib.Topology.MetricSpace.PositiveSquareHausdorff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Positive-gap rectangular dilation comparison

The actual positive row-Gram spectral sets inherit a quantitative
Hausdorff comparison from their Hermitian dilations. The positive gap
excludes matching to the dilation's extra zero spectrum. Arbitrary
C*-algebra entries retain continuous free spectra.
Source: arXiv:2406.11453v2, Section 5.3.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix
namespace CStarMatrix
variable {m n A B : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [Nonempty m] [Nontrivial A] [Nontrivial B]

end CStarMatrix
