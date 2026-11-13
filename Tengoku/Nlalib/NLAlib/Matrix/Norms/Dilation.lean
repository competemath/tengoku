import Tengoku.Nlalib.NLAlib.Matrix.Functions.DilationIdentities
import Tengoku.Nlalib.NLAlib.Matrix.Norms.Reindex

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Dilation norm on arbitrary finite coordinate labels

The existing finite-dimensional dilation theorem transports through ordinary
row and column equivalences, retaining its exact spectral norm.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- The Hermitian dilation commutes with arbitrary row and column reindexing.-/
theorem dilation_reindex {m n p q : Type*} (A : Matrix m n ℂ)
    (em : m ≃ p) (en : n ≃ q) :
    dilation (A.reindex em en) =
      (dilation A).reindex (em.sumCongr en) (em.sumCongr en) := by
  ext (a | a) (b | b) <;>
    simp [dilation, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply]

end NLAlib
