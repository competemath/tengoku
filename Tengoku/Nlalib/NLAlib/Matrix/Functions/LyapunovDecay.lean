import Tengoku.Nlalib.NLAlib.Matrix.Functions.LogarithmicNorm
import Tengoku.Nlalib.NLAlib.Matrix.Functions.GeometricMeanIdentities
import Tengoku.Nlalib.NLAlib.Matrix.Functions.LyapunovCayley

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exponential decay from a strict Lyapunov certificate

Whitening a positive-definite certificate produces a generator with
strictly negative Hermitian part. The energy estimate then gives decay
for the original, possibly nonnormal, matrix by similarity. Together
with the Cayley construction this proves decay for every Hurwitz matrix.
-/

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

end NLAlib
