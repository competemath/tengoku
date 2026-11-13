import Tengoku.Nlalib.NLAlib.Matrix.Spectral.GramSingularValues
import Tengoku.Nlalib.NLAlib.Matrix.Subspaces.Projections

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# Invariances of singular values

`singularValues` (over `ℝ` or `ℂ`, on arbitrary finite index types) is invariant under conjugate
transposition, under left multiplication by a matrix `H` with orthonormal columns
(`HᴴH = 1`, in particular a unitary matrix) and under right multiplication by `Hᴴ` (in
particular by a unitary matrix), at every natural index including the padded zeros. Relabeling
invariance is `singularValues_reindex` (`SingularValueSpectrum.lean`).

Source: Horn–Johnson 2013, §2.6 and §7.3.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]

end NLAlib
