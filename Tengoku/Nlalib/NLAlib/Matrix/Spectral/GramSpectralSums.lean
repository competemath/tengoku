import Tengoku.Nlalib.NLAlib.Matrix.Spectral.SingularValueInvariance
import Tengoku.Nlalib.NLAlib.Matrix.Inequalities.TraceTail

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Spectral sums of the two Gram matrices

The two Gram matrices have the same nonzero spectrum with multiplicity.
Zero padding of singular values proves equality for any scalar test
vanishing at zero. Horn--Johnson, Matrix Analysis, Section 7.3.
-/

noncomputable section
open Matrix
namespace NLAlib
variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

end NLAlib
