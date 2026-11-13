import Tengoku.Nlalib.NLAlib.Matrix.Functions.ResolventDifferences
import Tengoku.Nlalib.NLAlib.Matrix.Basic.NormalizedTrace
import Tengoku.Seed.Analysis.Calculus.FDeriv.RestrictScalars
import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.Normed.Algebra.InverseDerivatives

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Derivatives of the Hermitian resolvent and its normalized trace

The actual complex Fréchet derivatives are rational block maps. On a
Hermitian base point the nonreal shift is invertible, so the formulas apply
on a genuine open matrix neighborhood. Restricting scalars then gives the
real derivatives used in Gaussian interpolation.
The geometric series also supplies the native iterated derivative of every
order as a finite sum of ordered resolvent insertion words.
Source: the supplied Cauchy-transform reroute, (comparison-L).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial ContinuousLinearMap
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

/-- Every iterated derivative of a nonreal Hermitian resolvent is its actual
finite ordered insertion sum. Directions may be arbitrary complex matrices;
only the base point is Hermitian. Order zero and empty matrix dimensions
are included.
Source: Brailovskaya–van Handel, arXiv:2201.05142v3, Lemma 6.9.
@isnad1 id=eq.2h5v.s9.4844daa1c79e from=translated src=- shape=3ca6f7b6 vocab=739e807d
-/
theorem _root_.Matrix.IsHermitian.iteratedFDeriv_resolvent_apply
    {A : M} (hA : A.IsHermitian) {ζ : ℂ} (hζ : ζ.im ≠ 0)
    {k : ℕ} (H : Fin k → M) :
    iteratedFDeriv ℂ k (fun B : M => resolvent B ζ) A H =
      ∑ σ : Equiv.Perm (Fin k),
        (List.ofFn (fun i => resolvent A ζ * H (σ i))).prod * resolvent A ζ := by
  apply _root_.iteratedFDeriv_resolvent_apply
  change IsUnit (algebraMap ℂ M ζ - A)
  simpa only [Algebra.algebraMap_eq_smul_one] using
    hA.isUnit_smul_one_sub_of_im_ne_zero hζ

private theorem isUnit_aeval_shift (ζ : ℂ) (A : M) (hA : A.IsHermitian)
    (hζ : ζ.im ≠ 0) : IsUnit (aeval A (C ζ-X)) := by
  simpa only [map_sub,aeval_C,aeval_X,Algebra.algebraMap_eq_smul_one] using
    hA.isUnit_smul_one_sub_of_im_ne_zero hζ

/-- The actual resolvent has the single-insertion Fréchet derivative on the
nonreal Hermitian domain. Source: the supplied Cauchy-transform reroute.
atlas: cauchy-transform-gaussian-universality (partial)
@isnad1 id=hasfderi.2h3v.s8.83db381d7fd5 from=translated src=- shape=37bca8c3 vocab=a78229b1
-/
theorem hasFDerivAt_resolvent_of_isHermitian (ζ : ℂ) (A : M)
    (hA : A.IsHermitian) (hζ : ζ.im ≠ 0) :
    HasFDerivAt (fun B : M => resolvent B ζ) (rationalBlockMap 1 (C ζ-X) A A) A := by
  have h := hasFDerivAt_rationalMatrixEval 1 (C ζ-X) A (isUnit_aeval_shift ζ A hA hζ)
  have he : (rationalMatrixEval 1 (C ζ-X) : M → M) = fun B => resolvent B ζ :=
    funext (rationalMatrixEval_resolvent ζ)
  rwa [he] at h

/-- The squared resolvent's actual Fréchet derivative is its diagonal first
insertion map. Source: the supplied Cauchy-transform reroute (comparison-L).
atlas: cauchy-transform-gaussian-universality (partial)
@isnad1 id=hasfderi.2h3v.s8.a37afb17820c from=translated src=- shape=ec681f24 vocab=019d658c
-/
theorem hasFDerivAt_resolvent_sq_of_isHermitian (ζ : ℂ) (A : M)
    (hA : A.IsHermitian) (hζ : ζ.im ≠ 0) :
    HasFDerivAt (fun B : M => (resolvent B ζ)^2)
      (rationalBlockMap 1 ((C ζ-X)^2) A A) A := by
  have hQ : IsUnit (aeval A ((C ζ-X)^2)) := by
    simpa only [map_pow] using (isUnit_aeval_shift ζ A hA hζ).pow 2
  have h := hasFDerivAt_rationalMatrixEval 1 ((C ζ-X)^2) A hQ
  have he : (rationalMatrixEval 1 ((C ζ-X)^2) : M → M) =
      fun B => (resolvent B ζ)^2 := funext (rationalMatrixEval_resolvent_sq ζ)
  rwa [he] at h

/-- Applying the squared resolvent derivative gives exactly the two ordered
three-resolvent words.
@isnad1 id=eq.2h4v.s9.4ed937f7e9bd from=translated src=- shape=7eefd687 vocab=0369fcc3
-/
theorem fderiv_resolvent_sq_apply (ζ : ℂ) (A H : M)
    (hA : A.IsHermitian) (hζ : ζ.im ≠ 0) :
    fderiv ℂ (fun B : M => (resolvent B ζ)^2) A H =
      resolventSquareDifference ζ A A H := by
  rw [(hasFDerivAt_resolvent_sq_of_isHermitian ζ A hA hζ).fderiv,
    rationalBlockMap_apply,rationalBlockDifference_resolvent_sq ζ A A H hA hA hζ]

/-- The normalized trace derivative as a continuous complex linear map.-/
def traceResolventDerivative (ζ : ℂ) (A : M) : M →L[ℂ] ℂ :=
  (normalizedTraceLinearMap : M →ₗ[ℂ] ℂ).toContinuousLinearMap.comp
    (rationalBlockMap 1 (C ζ-X) A A)

/-- Cyclicity puts the insertion direction in front of the squared resolvent.
@isnad1 id=eq.0h4v.s8.d9f1ac4cad58 from=translated src=- shape=673415e5 vocab=66734691
-/
theorem traceResolventDerivative_apply (ζ : ℂ) (A H : M) :
    traceResolventDerivative ζ A H = normalizedTrace (H * (resolvent A ζ)^2) := by
  simp only [traceResolventDerivative,ContinuousLinearMap.comp_apply,
    LinearMap.coe_toContinuousLinearMap',normalizedTraceLinearMap_apply,rationalBlockMap_apply]
  rw [rationalBlockDifference_resolvent]
  rw [Matrix.mul_assoc,normalizedTrace_mul_comm (resolvent A ζ) (H*resolvent A ζ),
    pow_two,Matrix.mul_assoc]

/-- The actual normalized trace resolvent has the advertised cyclic derivative.
Source: the supplied Cauchy-transform interpolation.
atlas: cauchy-transform-gaussian-universality (partial)
@isnad1 id=hasfderi.2h3v.s7.9bfa4b596e6f from=translated src=- shape=3210a4b5 vocab=0e75ce55
-/
theorem hasFDerivAt_normalizedTrace_resolvent (ζ : ℂ) (A : M)
    (hA : A.IsHermitian) (hζ : ζ.im ≠ 0) :
    HasFDerivAt (fun B : M => normalizedTrace (resolvent B ζ))
      (traceResolventDerivative ζ A) A := by
  exact ((normalizedTraceLinearMap : M →ₗ[ℂ] ℂ).toContinuousLinearMap.hasFDerivAt).comp A
    (hasFDerivAt_resolvent_of_isHermitian ζ A hA hζ)

/-- Restricting scalars yields the real derivative required by real Gaussian
coordinates, without changing the actual trace-resolvent function.
@isnad1 id=hasfderi.2h3v.s8.883493e9c526 from=translated src=- shape=76002fc4 vocab=3e19351e
-/
theorem hasFDerivAt_normalizedTrace_resolvent_real (ζ : ℂ) (A : M)
    (hA : A.IsHermitian) (hζ : ζ.im ≠ 0) :
    HasFDerivAt (fun B : M => normalizedTrace (resolvent B ζ))
      ((traceResolventDerivative ζ A).restrictScalars ℝ) A :=
  (hasFDerivAt_normalizedTrace_resolvent ζ A hA hζ).restrictScalars ℝ

end NLAlib
