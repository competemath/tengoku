import Tengoku.Nlalib.NLAlib.Probability.Free.WordMatrixClosedAlgebra
import Tengoku.Nlalib.NLAlib.ForMathlib.MeasureTheory.TracialGramMoments

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Native vacuum Gram moments under actual norm perturbations

The native amplified vacuum is restricted to the genuine norm-closed
matrix field algebra before invoking tracial moment estimates. Its norm is
the inherited native amplified norm. No trace on all Hilbert operators is
claimed or assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Classical ComplexOrder

namespace NLAlib

variable {D ι : Type*} [Fintype D] [DecidableEq D]
local notation "W" => WordHilbertSpace ι
local notation "M" => CStarMatrix D D (W →L[ℂ] W)

end NLAlib

end
