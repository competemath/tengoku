import Tengoku.Nlalib.NLAlib.Sketching.Properties.SubspaceEmbedding.Gram
import Tengoku.Nlalib.NLAlib.Matrix.Spectral.SpectralBounds
import Tengoku.Nlalib.NLAlib.Matrix.Spectral.SingularValueSpectrum
import Tengoku.Nlalib.NLAlib.Matrix.Norms.Reindex

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# The singular-value form of a subspace embedding

Atlas: `ose-def`, `svd`. The finite list is indexed by the domain dimension
(`j : Fin (card n)`), so zero singular values of a wide matrix are included. Empty frames give
an empty list and the equivalence remains valid. Row and column indices are arbitrary finite
types; the `Fin` case is the base, transported by `singularValues_reindex`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p] [DecidableEq n]

omit [Fintype n] in
/-- Equivalent labels preserve Gram error as an exact matrix identity.
Horn–Johnson §5.6; atlas `ose-def`, `svd`.-/
theorem transpose_mul_self_sub_one_reindex {q : Type*} [Fintype q] [DecidableEq q]
    (A : Matrix m n ℝ) (em : m ≃ p) (en : n ≃ q) :
    (A.reindex em en)ᵀ * (A.reindex em en) - 1 = (Aᵀ * A - 1).reindex en en := by
  simp only [Matrix.reindex_apply, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]
  change (Aᵀ * A).submatrix en.symm en.symm - 1 =
    (Aᵀ * A).submatrix en.symm en.symm - (1 : Matrix n n ℝ).submatrix en.symm en.symm
  rw [Matrix.submatrix_one_equiv]

end NLAlib
