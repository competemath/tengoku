import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.CStarAlgebra.CStarMatrixPiLp
import Tengoku.Nlalib.NLAlib.Probability.Free.WordFields
import Tengoku.Nlalib.NLAlib.Matrix.Norms.Core

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Actual compatible matrix amplification of the concrete word operators

Scalar matrix coefficients act faithfully and isometrically on the native
Hilbert direct sum of word Hilbert spaces. Operator-valued coefficient blocks
use the canonical `CStarMatrix` representation; they do not use the scalar
Euclidean matrix adapter or a new matrix norm. This supplies actual bounded
self-adjoint matrix-valued reference linear combinations.

No faithful amplified state, free law, or spectral comparison is assumed.
-/

noncomputable section
set_option autoImplicit false

open scoped Classical ComplexOrder

namespace NLAlib

/-- The actual finite matrix amplification of the concrete word Hilbert
space, equipped with its native Hilbert direct-sum norm.-/
abbrev WordMatrixHilbertSpace (D ι : Type*) := PiLp 2 (fun _ : D => WordHilbertSpace ι)

variable {D ι : Type*} [Fintype D] [DecidableEq D]
local notation "W" => WordHilbertSpace ι
local notation "K" => WordMatrixHilbertSpace D ι
local notation "B" => W →L[ℂ] W

/-- Actual scalar C*-matrix coefficients act on the word Hilbert direct sum
by the canonical faithful bounded block representation.-/
def wordCStarCoefficientHom : CStarMatrix D D ℂ →⋆ₐ[ℂ] (K →L[ℂ] K) :=
  CStarMatrix.toPiLpStarAlgHom.comp (CStarMatrix.mapStarAlgHom (StarAlgHom.ofId ℂ B))

private theorem word_scalar_operator_injective :
    Function.Injective (StarAlgHom.ofId ℂ B) := by
  intro z w hzw
  have h := congrArg (wordVacuumExpectation ι) hzw
  simpa only [StarAlgHom.ofId_apply, Algebra.algebraMap_eq_smul_one,
    map_smul, wordVacuumExpectation_one, smul_eq_mul, mul_one] using h

/-- The coefficient representation is injective, proved from the actual
normalized vacuum rather than any nontriviality assumption on the alphabet.
@isnad1 id=injectiv.0h2v.s14.52b6426dd125 from=translated src=- shape=b702916c vocab=eab016b6
-/
theorem wordCStarCoefficientHom_injective :
    Function.Injective (wordCStarCoefficientHom (D := D) (ι := ι)) :=
  CStarMatrix.toPiLpStarAlgHom_injective.comp
    (CStarMatrix.mapStarAlgHom_injective _ word_scalar_operator_injective)

/-- Scalar C*-matrix coefficients retain exactly their canonical native norm
in the actual amplified word representation, including empty matrix dimension.
@isnad1 id=eq.0h3v.s14.8bd5cc01fd1a from=translated src=- shape=2d7f129e vocab=55e63362
-/
theorem norm_wordCStarCoefficientHom (A : CStarMatrix D D ℂ) :
    ‖wordCStarCoefficientHom (ι := ι) A‖ = ‖A‖ :=
  NonUnitalStarAlgHom.norm_map wordCStarCoefficientHom wordCStarCoefficientHom_injective A

/-- The genuine scalar matrix-coefficient embedding, bundled as a native
star-algebra homomorphism into bounded operators on the word direct sum.-/
def wordMatrixCoefficientHom : Matrix D D ℂ →⋆ₐ[ℂ] (K →L[ℂ] K) :=
  wordCStarCoefficientHom.comp CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom

/-- The actual coordinate action of a scalar matrix coefficient.
@isnad1 id=eq.0h5v.s15.ee7c4c5b72b4 from=translated src=- shape=0639d250 vocab=5f8ed6cf
-/
@[simp]
theorem wordMatrixCoefficientHom_apply (A : Matrix D D ℂ) (v : K) (i : D) :
    wordMatrixCoefficientHom A v i = ∑ j, A i j • v j := by
  simp [wordMatrixCoefficientHom, wordCStarCoefficientHom,
    StarAlgHom.ofId_apply, Algebra.algebraMap_eq_smul_one]
  rfl

open scoped Matrix.Norms.L2Operator in
/-- The actual scalar coefficient embedding preserves the named matrix
spectral norm exactly, with no dimension factor.
@isnad1 id=eq.0h3v.s14.ed9cdee0d8ad from=translated src=- shape=e437734d vocab=e3ada602
-/
theorem norm_wordMatrixCoefficientHom (A : Matrix D D ℂ) :
    ‖wordMatrixCoefficientHom (ι := ι) A‖ = specNorm A := by
  change ‖wordCStarCoefficientHom (CStarMatrix.ofMatrix A)‖ = specNorm A
  rw [norm_wordCStarCoefficientHom, CStarMatrix.norm_ofMatrix_complex]
  exact (specNorm_eq_norm A).symm

/-- A Hermitian scalar matrix coefficient gives an actual self-adjoint
bounded operator under the compatible coefficient embedding.
@isnad1 id=isselfad.1h3v.s14.944bfc61500d from=translated src=- shape=d6187628 vocab=7dd20e53
-/
theorem isSelfAdjoint_wordMatrixCoefficientHom {A : Matrix D D ℂ} (hA : A.IsHermitian) :
    IsSelfAdjoint (wordMatrixCoefficientHom (ι := ι) A) :=
  hA.isSelfAdjoint.map wordMatrixCoefficientHom

/-- An actual scalar matrix coefficient tensored with an actual bounded
word-space operator, realized by native bounded-operator matrix entries.-/
def wordMatrixTensor (A : Matrix D D ℂ) (T : B) : K →L[ℂ] K :=
  CStarMatrix.toPiLpStarAlgHom (D := D) (H := W)
    (CStarMatrix.ofMatrix (fun i j => A i j • T))

/-- The concrete coefficient-operator block action has the expected finite
column formula. No tensor product completion is assumed.
@isnad1 id=eq.0h6v.s14.09f8b1764b2c from=translated src=- shape=be025ffd vocab=28acdd55
-/
@[simp]
theorem wordMatrixTensor_apply (A : Matrix D D ℂ) (T : B) (v : K) (i : D) :
    wordMatrixTensor A T v i = ∑ j, A i j • T (v j) := by
  simp [wordMatrixTensor, CStarMatrix.ofMatrix]
  rfl

/-- The identity coefficient amplifies a word-space operator diagonally.
@isnad1 id=eq.0h5v.s13.a3d41c7b08a8 from=translated src=- shape=0064eb5e vocab=3b5f02b6
-/
@[simp]
theorem wordMatrixTensor_one_apply (T : B) (v : K) (i : D) :
    wordMatrixTensor (1 : Matrix D D ℂ) T v i = T (v i) := by
  rw [wordMatrixTensor_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Ne.symm hji]
  · simp

/-- The actual coefficient-operator block factors as its scalar coefficient
embedding times the diagonal amplification of its word-space operator.
@isnad1 id=eq.0h4v.s15.49061710845e from=translated src=- shape=4c8b0878 vocab=2cca38aa
-/
theorem wordMatrixTensor_eq_coefficient_mul (A : Matrix D D ℂ) (T : B) :
    wordMatrixTensor A T = wordMatrixCoefficientHom A * wordMatrixTensor 1 T := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  change wordMatrixTensor A T v i =
    wordMatrixCoefficientHom A (wordMatrixTensor 1 T v) i
  rw [wordMatrixTensor_apply, wordMatrixCoefficientHom_apply]
  simp only [wordMatrixTensor_one_apply]

/-- Actual scalar matrix coefficients commute with every diagonal
word-space operator amplification, from complex linearity of that operator.
@isnad1 id=commute.0h4v.s14.9810b89c745f from=translated src=- shape=541542d2 vocab=b3ffb754
-/
theorem commute_wordMatrixCoefficientHom_wordMatrixTensor_one (A : Matrix D D ℂ) (T : B) :
    Commute (wordMatrixCoefficientHom A) (wordMatrixTensor 1 T) := by
  change _ * _ = _ * _
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
    wordMatrixCoefficientHom_apply, wordMatrixTensor_one_apply, map_sum, map_smul]

/-- The actual coefficient-operator block uses precisely the canonical
native C*-matrix norm, with no new norm chosen for raw matrix entries.
@isnad1 id=eq.0h4v.s15.593cb954a537 from=translated src=- shape=918e3a63 vocab=873dcd0b
-/
theorem norm_wordMatrixTensor (A : Matrix D D ℂ) (T : B) :
    ‖wordMatrixTensor A T‖ = ‖CStarMatrix.ofMatrix (fun i j => A i j • T)‖ :=
  CStarMatrix.norm_toPiLpStarAlgHom _

/-- Hermitian coefficients and self-adjoint word-space operators yield a
genuine self-adjoint amplified block operator.
@isnad1 id=isselfad.2h4v.s13.64144acaec67 from=translated src=- shape=3085ffbc vocab=5139f25f
-/
theorem isSelfAdjoint_wordMatrixTensor {A : Matrix D D ℂ} (hA : A.IsHermitian)
    {T : B} (hT : IsSelfAdjoint T) : IsSelfAdjoint (wordMatrixTensor A T) := by
  apply (CStarMatrix.isSelfAdjoint_toPiLpStarAlgHom_iff _).mpr
  change star (CStarMatrix.ofMatrix (fun i j => A i j • T)) =
    CStarMatrix.ofMatrix (fun i j => A i j • T)
  apply CStarMatrix.ext
  intro i j
  change star (A j i • T) = A i j • T
  rw [star_smul, hT.star_eq, hA.apply]

/-- The actual matrix-coefficient linear reference on the concrete
Hilbert space. Its operator norm and spectrum are native bounded-operator ones.-/
def wordMatrixLinearCombination [Fintype ι] (A₀ : Matrix D D ℂ)
    (A : ι → Matrix D D ℂ) : K →L[ℂ] K :=
  wordMatrixCoefficientHom A₀ + ∑ i, wordMatrixTensor (A i) (wordField i)

/-- Actual Hermitian matrix coefficients give a self-adjoint concrete
matrix-amplified linear reference operator.
@isnad1 id=isselfad.2h4v.s12.309f8e9e9b87 from=translated src=- shape=f98adeaa vocab=9ed27740
-/
theorem isSelfAdjoint_wordMatrixLinearCombination [Fintype ι]
    {A₀ : Matrix D D ℂ} (hA₀ : A₀.IsHermitian) {A : ι → Matrix D D ℂ}
    (hA : ∀ i, (A i).IsHermitian) : IsSelfAdjoint (wordMatrixLinearCombination A₀ A) := by
  unfold wordMatrixLinearCombination
  exact IsSelfAdjoint.add (R := K →L[ℂ] K)
    (isSelfAdjoint_wordMatrixCoefficientHom (ι := ι) hA₀)
    (isSelfAdjoint_sum _ (fun i _ =>
      isSelfAdjoint_wordMatrixTensor (hA i) (isSelfAdjoint_wordField i)))

end NLAlib
