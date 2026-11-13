import Tengoku.Nlalib.NLAlib.Matrix.Functions.RationalBlockMaps
import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.ContinuousSecant
import Tengoku.Seed.Analysis.Calculus.FDeriv.Congr

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Full Fréchet derivatives of rational matrix functions

Exact finite differences and continuity of their linear maps prove both
Fréchet derivatives on the open nonsingular-denominator domain.
The second derivative is the sum of both ordered insertion maps.
Source: matrix-toolkit derivations, F18--F19.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial Filter ContinuousLinearMap
open scoped Matrix.Norms.L2Operator Topology
namespace NLAlib
variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n 𝕜
private local instance : ContinuousAdd (M →L[𝕜] M →L[𝕜] M) :=
  (inferInstance : IsTopologicalAddGroup (M →L[𝕜] M →L[𝕜] M)).toContinuousAdd

/-- Rational matrix functions have an open denominator domain.
@isnad1 id=isopen.0h3v.s8.2c1e7b9113d8 from=translated src=- shape=d641897d vocab=0753ba3a
-/
theorem isOpen_rationalMatrixDomain (Q : 𝕜[X]) :
    IsOpen {A : M | IsUnit (aeval A Q)} :=
  Units.isOpen.preimage (continuous_iff_continuousAt.mpr
    (fun A => (Q.hasFDerivAt_aeval_noncomm A).continuousAt))

/--
@isnad1 id=eventual.1h4v.s9.b8bd80bbf97c from=translated src=- shape=952073f2 vocab=5270ef13
-/
theorem eventually_isUnit_aeval (Q : 𝕜[X]) (A : M) (hA : IsUnit (aeval A Q)) :
    ∀ᶠ B in 𝓝 A, IsUnit (aeval B Q) :=
  (isOpen_rationalMatrixDomain (n := n) Q).mem_nhds hA

/-- The full Fréchet derivative is the first block difference on the diagonal.
Source: F19.
atlas: matrix-function-block-divided-differences (partial)
@isnad1 id=hasfderi.1h5v.s9.0b619911deb4 from=translated src=- shape=4681df00 vocab=e2814e77
-/
theorem hasFDerivAt_rationalMatrixEval (P Q : 𝕜[X]) (A : M)
    (hA : IsUnit (aeval A Q)) :
    HasFDerivAt (rationalMatrixEval P Q) (rationalBlockMap P Q A A) A := by
  apply hasFDerivAt_of_continuous_secant (L := fun B => rationalBlockMap P Q B A)
  · simpa only [Function.comp_def] using
      (continuousAt_rationalBlockMap P Q A A hA hA).comp
        (x := A) (f := fun B : M => (B,A)) (continuous_id.prodMk continuous_const).continuousAt
  · filter_upwards [eventually_isUnit_aeval Q A hA] with B hB
    simpa only [rationalBlockMap_apply] using rationalMatrixEval_sub P Q B A hB hA

/-- The continuous bilinear Hessian is the sum of the two insertion orders.-/
def rationalMatrixHessian (P Q : 𝕜[X]) (A : M) : M →L[𝕜] M →L[𝕜] M :=
  rationalSecondBlockMap P Q A A A + (rationalSecondBlockMap P Q A A A).flip

/--
@isnad1 id=eq.0h7v.s11.5f72afe56385 from=translated src=- shape=9380e158 vocab=fe0fd04d
-/
@[simp] theorem rationalMatrixHessian_apply (P Q : 𝕜[X]) (A G H : M) :
    rationalMatrixHessian P Q A G H = rationalSecondBlockDifference P Q A A A G H +
      rationalSecondBlockDifference P Q A A A H G := by
  simp [rationalMatrixHessian]

/-- Differentiating the first difference on its diagonal gives both ordered
second differences, as an operator-norm Fréchet derivative.
Source: F19.
atlas: matrix-function-block-divided-differences (partial)
@isnad1 id=hasfderi.1h5v.s10.80f3363761df from=translated src=- shape=04d24df0 vocab=e411c773
-/
theorem hasFDerivAt_rationalBlockMap_diagonal (P Q : 𝕜[X]) (A : M)
    (hA : IsUnit (aeval A Q)) :
    HasFDerivAt (fun B : M => rationalBlockMap P Q B B) (rationalMatrixHessian P Q A) A := by
  let L : M → M →L[𝕜] M →L[𝕜] M := fun B =>
    rationalSecondBlockMap P Q B A B + (rationalSecondBlockMap P Q A B A).flip
  change HasFDerivAt _ (L A) A
  apply hasFDerivAt_of_continuous_secant
  · have h₁ : ContinuousAt (fun B : M => rationalSecondBlockMap P Q B A B) A := by
      simpa only [Function.comp_def] using
        (continuousAt_rationalSecondBlockMap P Q A A A hA hA hA).comp
          (x := A) (f := fun B : M => (B,A,B))
          (continuous_id.prodMk (continuous_const.prodMk continuous_id)).continuousAt
    have h₂ : ContinuousAt (fun B : M => rationalSecondBlockMap P Q A B A) A := by
      simpa only [Function.comp_def] using
        (continuousAt_rationalSecondBlockMap P Q A A A hA hA hA).comp
          (x := A) (f := fun B : M => (A,B,A))
          (continuous_const.prodMk (continuous_id.prodMk continuous_const)).continuousAt
    exact h₁.add (continuous_flip_matrixBilinear.continuousAt.comp h₂)
  · filter_upwards [eventually_isUnit_aeval Q A hA] with B hB
    ext H i j
    have h₁ := congrArg (fun D : M => D i j)
      (rationalBlockDifference_sub_left P Q B A B H hB hA hB)
    have h₂ := congrArg (fun D : M => D i j)
      (rationalBlockDifference_sub_right P Q A B A H hA hB hA)
    simp only [Matrix.sub_apply] at h₁ h₂
    simp only [sub_apply, rationalBlockMap_apply, L, add_apply, flip_apply,
      rationalSecondBlockMap_apply, Matrix.add_apply, Matrix.sub_apply]
    calc
      _ = (rationalBlockDifference P Q B B H i j - rationalBlockDifference P Q A B H i j) +
          (rationalBlockDifference P Q A B H i j - rationalBlockDifference P Q A A H i j) := by abel
      _ = _ := by rw [h₁, h₂]

/-- The actual Fréchet derivative of the rational calculus is differentiable,
with Hessian the symmetrized ordered second difference.
Source: F19.
atlas: matrix-function-block-divided-differences (partial)
@isnad1 id=hasfderi.1h5v.s10.4a9c7acd40a2 from=translated src=- shape=8157f1a6 vocab=ff533f96
-/
theorem hasFDerivAt_fderiv_rationalMatrixEval (P Q : 𝕜[X]) (A : M)
    (hA : IsUnit (aeval A Q)) :
    HasFDerivAt (fun B : M => fderiv 𝕜 (rationalMatrixEval P Q) B)
      (rationalMatrixHessian P Q A) A := by
  apply (hasFDerivAt_rationalBlockMap_diagonal P Q A hA).congr_of_eventuallyEq
  filter_upwards [eventually_isUnit_aeval Q A hA] with B hB
  exact (hasFDerivAt_rationalMatrixEval P Q B hB).fderiv

/-- Applying the actual first Fréchet derivative gives the triangular block
difference. Source: F19.
atlas: matrix-function-block-divided-differences (partial)
@isnad1 id=eq.1h6v.s10.928c68114e22 from=translated src=- shape=931ab0bf vocab=53f3f657
-/
theorem fderiv_rationalMatrixEval_apply (P Q : 𝕜[X]) (A H : M)
    (hA : IsUnit (aeval A Q)) :
    fderiv 𝕜 (rationalMatrixEval P Q) A H = rationalBlockDifference P Q A A H := by
  rw [(hasFDerivAt_rationalMatrixEval P Q A hA).fderiv, rationalBlockMap_apply]

/-- The actual second Fréchet derivative is the sum of the two ordered
second block differences. Source: F19.
atlas: matrix-function-block-divided-differences (partial)
@isnad1 id=eq.1h7v.s12.a8e2eaba235f from=translated src=- shape=5c22f064 vocab=4a040ad5
-/
theorem fderiv_fderiv_rationalMatrixEval_apply (P Q : 𝕜[X]) (A G H : M)
    (hA : IsUnit (aeval A Q)) :
    fderiv 𝕜 (fun B : M => fderiv 𝕜 (rationalMatrixEval P Q) B) A G H =
      rationalSecondBlockDifference P Q A A A G H +
        rationalSecondBlockDifference P Q A A A H G := by
  rw [(hasFDerivAt_fderiv_rationalMatrixEval P Q A hA).fderiv,
    rationalMatrixHessian_apply]

end NLAlib
