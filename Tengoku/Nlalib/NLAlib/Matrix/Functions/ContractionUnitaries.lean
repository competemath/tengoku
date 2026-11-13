import Tengoku.Nlalib.NLAlib.Matrix.Spectral.SpectralBounds
import Tengoku.Nlalib.NLAlib.Matrix.Spectral.SVD

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A complex contraction is the average of two unitaries

The construction uses the actual indexed SVD and the scalar circle points
`s ± i sqrt(1-s²)`. Tropp (2022), Proposition 12.24.
-/

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
namespace NLAlib

end NLAlib
