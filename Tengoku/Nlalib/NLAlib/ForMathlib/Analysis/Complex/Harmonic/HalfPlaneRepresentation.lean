import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.Complex.Harmonic.HerglotzRepresentation
import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.Complex.CayleyTransform

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Positive-imaginary holomorphic functions in Cayley coordinates

Transport the proved disk Herglotz representation to the upper half plane.
The positive measure still lives on the compact circle; finite real-line
Stieltjes mass requires the additional asymptotic normalization.
Source: Ajanki--Erdos--Kruger (2019), Proposition 2.1,
arXiv:1604.08188v5.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Metric Set

namespace Complex

end Complex
