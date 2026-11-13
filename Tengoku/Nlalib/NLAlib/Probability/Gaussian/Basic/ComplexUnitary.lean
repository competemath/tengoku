import Tengoku.Nlalib.NLAlib.Probability.Gaussian.Basic.CircularComplex
import Tengoku.Nlalib.NLAlib.Probability.Gaussian.Basic.OrthogonalVector
import Tengoku.Nlalib.NLAlib.Matrix.Structured.Realification

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Unitary invariance of circular complex Gaussian vectors

The joint product law, and hence independence of complex coordinates, is
preserved by a unitary change of coordinates. The more general rectangular
coisometry statement also permits selecting a smaller orthonormal coordinate
family. Each real and imaginary input coordinate has distribution `N(0,1)`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Multiplication by an actual complex matrix agrees with multiplication by
its realification in the real and imaginary coordinate copies.
@isnad1 id=eq.0h4v.s6.4426df0b482a from=translated src=- shape=2a6040a4 vocab=01de8f62
-/
theorem complexifyVector_mulVec_realification (U : Matrix m n ℂ) (x : n ⊕ n → ℝ) :
    complexifyVector (matrixRealification U *ᵥ x) = U *ᵥ complexifyVector x := by
  funext i
  apply Complex.ext <;>
    simp [complexifyVector, matrixRealification, Matrix.fromBlocks, Matrix.mulVec,
      dotProduct, Fintype.sum_sum_type, Complex.mul_re, Complex.mul_im,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, neg_mul, add_comm, sub_eq_add_neg]

/-- A complex matrix with orthonormal rows maps an actual circular complex
Gaussian product law to the corresponding target product law. The independent
real and imaginary coordinates all have variance one. This statement includes
rectangular coisometries and empty coordinate types.
atlas: gaussian-cayley-fourier-block-law (partial)
@isnad1 id=haslaw.1h3v.s6.860804e0b882 from=translated src=- shape=ed4e1f31 vocab=d869a2a5
-/
theorem hasLaw_mulVec_circularComplexGaussianVector_orthonormalRows
    (U : Matrix m n ℂ) (hU : HasOrthonormalCols Uᴴ) :
    HasLaw (fun z => U *ᵥ z) (circularComplexGaussianVector m)
      (circularComplexGaussianVector n) := by
  have hR : HasOrthonormalCols (matrixRealification U)ᵀ := by
    rw [← matrixRealification_conjTranspose]
    exact hU.realification
  have hreal := hasLaw_mulVec_gaussianVector_orthonormalRows (matrixRealification U) hR
  have hresult := (hasLaw_complexifyVector_gaussianVector (n := m)).comp hreal
  refine ⟨(by fun_prop : Measurable (fun z : n → ℂ => U *ᵥ z)).aemeasurable, ?_⟩
  rw [← (hasLaw_complexifyVector_gaussianVector (n := n)).map_eq,
    Measure.map_map (by fun_prop) (by fun_prop)]
  have hf : (fun z : n → ℂ => U *ᵥ z) ∘ complexifyVector =
      complexifyVector ∘ (fun x => matrixRealification U *ᵥ x) := by
    funext x
    exact (complexifyVector_mulVec_realification U x).symm
  rw [hf]
  exact hresult.map_eq

/-- A square unitary matrix preserves the full circular complex Gaussian
product law. Both real components of every coordinate are standard normals.
atlas: gaussian-cayley-fourier-block-law (partial)
@isnad1 id=haslaw.1h2v.s6.14f8caf094bd from=translated src=- shape=2f44b095 vocab=5a7e1620
-/
theorem hasLaw_mulVec_circularComplexGaussianVector_unitary
    (U : Matrix n n ℂ) (hU : HasOrthonormalCols U) :
    HasLaw (fun z => U *ᵥ z) (circularComplexGaussianVector n)
      (circularComplexGaussianVector n) := by
  apply hasLaw_mulVec_circularComplexGaussianVector_orthonormalRows U
  change Uᴴᴴ * Uᴴ = 1
  rw [Matrix.conjTranspose_conjTranspose]
  exact mul_eq_one_comm.mp hU

/-- The orthonormal-row complex Gaussian transform applies to a random vector
on any sample space using its actual joint circular complex Gaussian law.
atlas: gaussian-cayley-fourier-block-law (partial)
@isnad1 id=haslaw.2h6v.s7.9342350e0ab2 from=translated src=- shape=78269da6 vocab=c3764398
-/
theorem hasLaw_mulVec_circularComplexGaussianVector_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : Ω → n → ℂ}
    (hZ : HasLaw Z (circularComplexGaussianVector n) μ)
    (U : Matrix m n ℂ) (hU : HasOrthonormalCols Uᴴ) :
    HasLaw (fun ω => U *ᵥ Z ω) (circularComplexGaussianVector m) μ :=
  (hasLaw_mulVec_circularComplexGaussianVector_orthonormalRows U hU).comp hZ

/-- Coordinates after a rectangular complex coisometry are independent
complex random variables, with the full circular complex Gaussian law.
@isnad1 id=iindepfu.2h6v.s6.34bf609b6fb8 from=translated src=- shape=fada4317 vocab=59353d41
-/
theorem iIndepFun_mulVec_circularComplexGaussianVector_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : Ω → n → ℂ}
    (hZ : HasLaw Z (circularComplexGaussianVector n) μ)
    (U : Matrix m n ℂ) (hU : HasOrthonormalCols Uᴴ) :
    iIndepFun (fun i ω => (U *ᵥ Z ω) i) μ :=
  (hasLaw_mulVec_circularComplexGaussianVector_of_hasLaw hZ U hU).iIndepFun_eval_of_circularComplexGaussianVector

/-- All transformed real and imaginary entries together have the full product
standard-real-Gaussian law, including independence between the two parts.
atlas: gaussian-cayley-fourier-block-law (partial)
@isnad1 id=haslaw.2h6v.s7.711579172a9f from=translated src=- shape=fe9fc457 vocab=82a73493
-/
theorem hasLaw_realify_mulVec_circularComplexGaussianVector_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : Ω → n → ℂ}
    (hZ : HasLaw Z (circularComplexGaussianVector n) μ)
    (U : Matrix m n ℂ) (hU : HasOrthonormalCols Uᴴ) :
    HasLaw (fun ω => realifyVector (U *ᵥ Z ω)) (gaussianVector (m ⊕ m)) μ :=
  hasLaw_realifyVector_circularComplexGaussianVector.comp
    (hasLaw_mulVec_circularComplexGaussianVector_of_hasLaw hZ U hU)

/-- Every transformed real and imaginary coordinate is independent of all the
others, under the actual sample-space law.
atlas: gaussian-cayley-fourier-block-law (partial)
@isnad1 id=iindepfu.2h6v.s7.62efc8783319 from=translated src=- shape=bebb56f3 vocab=e97a6891
-/
theorem iIndepFun_realify_mulVec_circularComplexGaussianVector_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : Ω → n → ℂ}
    (hZ : HasLaw Z (circularComplexGaussianVector n) μ)
    (U : Matrix m n ℂ) (hU : HasOrthonormalCols Uᴴ) :
    iIndepFun (fun i ω => realifyVector (U *ᵥ Z ω) i) μ :=
  (hasLaw_realify_mulVec_circularComplexGaussianVector_of_hasLaw hZ U hU).iIndepFun_eval_of_gaussianVector

end NLAlib
