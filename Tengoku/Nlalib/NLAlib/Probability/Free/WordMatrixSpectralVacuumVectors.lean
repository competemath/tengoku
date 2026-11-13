import Tengoku.Nlalib.NLAlib.Probability.Free.WordMatrixVacuumEmbedding
import Tengoku.Nlalib.NLAlib.Probability.Free.WordMatrixSpectrum
import Tengoku.Seed.Analysis.Matrix.Spectrum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Actual approximate spectral vectors inside the amplified vacuum subspace

A free spectral point is close to a genuine mean eigenvalue. Its actual
unit matrix eigenvector, tensored with the genuine word vacuum, has shifted
residual at most five times the imaginary height above the free-series
scale. This is the geometric input to the large-height moment estimate.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical ComplexOrder

namespace NLAlib

variable {D ι : Type*} [Fintype D] [DecidableEq D] [Fintype ι]
local notation "W" => WordHilbertSpace ι
local notation "K" => WordMatrixHilbertSpace D ι

omit [Fintype ι] in
/-- A genuine coefficient eigenvector remains an actual eigenvector of its
matrix mean after embedding into the existing vacuum subspace.
@isnad1 id=eq.1h4v.s15.ce806314f11e from=translated src=- shape=43ddfcb6 vocab=c4e5bf4e
-/
theorem wordMatrixCoefficientHom_wordMatrixVacuumEmbedding_eigenvector
    {A₀ : Matrix D D ℂ} (hA₀ : A₀.IsHermitian) (k : D) :
    wordMatrixCoefficientHom A₀ (wordMatrixVacuumEmbedding (ι := ι) (hA₀.eigenvectorBasis k)) =
      (hA₀.eigenvalues k : ℂ)•
        wordMatrixVacuumEmbedding (ι := ι) (hA₀.eigenvectorBasis k) := by
  apply PiLp.ext
  intro i
  rw [wordMatrixCoefficientHom_apply]
  simp only [PiLp.smul_apply,wordMatrixVacuumEmbedding_apply,smul_smul]
  rw [← Finset.sum_smul]
  have he := congrFun (hA₀.mulVec_eigenvectorBasis k) i
  change (∑ j, A₀ i j*(hA₀.eigenvectorBasis k) j)=
    (hA₀.eigenvalues k : ℂ)*(hA₀.eigenvectorBasis k) i at he
  change (∑ j, A₀ i j*(hA₀.eigenvectorBasis k) j)•wordVacuum ι=
    ((hA₀.eigenvalues k : ℂ)*(hA₀.eigenvectorBasis k) i)•wordVacuum ι
  exact congrArg (fun c : ℂ => c•wordVacuum ι) he

end NLAlib

end
