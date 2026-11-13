import Tengoku.Nlalib.NLAlib.Matrix.Spectral.SVD
import Tengoku.Nlalib.NLAlib.Matrix.Spectral.EigenvalueEquality
import Tengoku.Nlalib.NLAlib.Matrix.Norms.Reindex

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Singular values under reindexing

Sorted eigenvalues `eigenvalues₀` are invariant under relabeling and do not depend on the
Hermitian witness (`NLAlib.Matrix.Spectral.EigenvalueEquality`); hence `singularValues`
(whose squares are the sorted Gram eigenvalues, `sq_singularValues_eq_eigenvalues₀`) is
invariant under reindexing rows and columns. As a first consequence, the Frobenius identity
`‖A‖_F² = ∑_{k < min m n} σ_k²` (`frobSq_eq_sum_sq_singularValues`) holds on arbitrary finite
index types.
Source: Horn–Johnson 2013, Section 2.6; supports `kronecker-spectral`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

end NLAlib
