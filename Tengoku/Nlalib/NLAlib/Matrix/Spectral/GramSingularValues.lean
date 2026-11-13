import Tengoku.Nlalib.NLAlib.Matrix.Spectral.SingularValueSpectrum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# Equal Gram matrices and singular values

Two matrices (over `ℝ` or `ℂ`) with the same column domain whose Gram matrices `AᴴA` have the
same characteristic polynomial (in particular, equal Gram matrices) have the same zero-padded
singular values, even with different row spaces.
Source: Horn–Johnson (2013), §2.6; supports QR, absolute functional calculus and
invariant-norm spectral variation.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq n]

end NLAlib
