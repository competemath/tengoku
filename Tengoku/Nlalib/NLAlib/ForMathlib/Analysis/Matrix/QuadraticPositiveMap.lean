import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.Matrix.QuadraticForm
import Tengoku.Seed.Analysis.CStarAlgebra.PositiveLinearMap
import Tengoku.Seed.Analysis.Matrix.Order
import Tengoku.Seed.LinearAlgebra.Complex.Module

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Positive matrix quadratic maps

The scalar quadratic probe is a positive complex-linear map. Native
positive-map star preservation therefore transports the matrix imaginary
part to the scalar imaginary part exactly.
-/

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule

/-- The imaginary self-adjoint part of a complex number is its imaginary
coordinate embedded into the complex numbers.
@isnad1 id=eq.0h1v.s8.53d38d771b4c from=translated src=- shape=ac4b5602 vocab=0d366fe3
-/
theorem Complex.coe_imaginaryPart (z : ℂ) : (imaginaryPart z : ℂ) = (z.im : ℂ) := by
  rw [imaginaryPart_apply_coe]
  apply Complex.ext <;>
    simp [Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im]
  ring

namespace Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A fixed-vector matrix quadratic probe as a positive complex-linear map.-/
def matrixQuadraticPositiveMap (v : n → ℂ) : Matrix n n ℂ →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (matrixQuadraticFormCLM v).toLinearMap
    (fun _ hA => hA.posSemidef.dotProduct_mulVec_nonneg v)

omit [DecidableEq n] in
/--
@isnad1 id=eq.0h3v.s7.5c5b837384f9 from=translated src=- shape=df32d730 vocab=6f4c72cb
-/
@[simp] theorem matrixQuadraticPositiveMap_apply (v : n → ℂ) (A : Matrix n n ℂ) :
    matrixQuadraticPositiveMap v A = matrixQuadraticFormCLM v A := rfl

/-- Scalar imaginary quadratic forms are the real quadratic forms of
the native matrix imaginary part.
@isnad1 id=eq.0h3v.s10.2a88cadcece1 from=translated src=- shape=61017606 vocab=9b839739
-/
theorem im_matrixQuadraticFormCLM (v : n → ℂ) (A : Matrix n n ℂ) :
    (matrixQuadraticFormCLM v A).im =
      matrixRealQuadraticFormCLM v (imaginaryPart A : Matrix n n ℂ) := by
  have h := map_imaginaryPart (matrixQuadraticPositiveMap v) A
  rw [Complex.coe_imaginaryPart] at h
  exact (congrArg Complex.re h).symm

/-- Positive semidefinite matrix imaginary part gives nonnegative scalar
imaginary part for every deterministic quadratic probe.
@isnad1 id=le.1h3v.s10.3d99b64125e3 from=translated src=- shape=2cf8d492 vocab=a598afdb
-/
theorem im_matrixQuadraticFormCLM_nonneg (v : n → ℂ) (A : Matrix n n ℂ)
    (hA : Matrix.PosSemidef (imaginaryPart A : Matrix n n ℂ)) :
    0 ≤ (matrixQuadraticFormCLM v A).im := by
  rw [im_matrixQuadraticFormCLM]
  exact hA.re_dotProduct_nonneg v

end Matrix
