import Tengoku.Nlalib.NLAlib.Matrix.Functions.HermitianResolvent
import Tengoku.Nlalib.NLAlib.Matrix.Functions.RationalBlockOperations
import Tengoku.Nlalib.NLAlib.Matrix.Functions.RationalDerivatives

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ordered differences of the squared resolvent

The explicit first and ordered second insertion words are specializations of
the native rational block calculus. Their finite-difference and derivative
identities therefore retain the specified insertion order.
Source: supplied Cauchy-transform reroute, (comparison-L)–(comparison-T).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- First insertion difference of the squared resolvent.-/
def resolventSquareDifference (ζ : ℂ) (A B H : Matrix n n ℂ) : Matrix n n ℂ :=
  (resolvent A ζ)^2 * H * resolvent B ζ +
    resolvent A ζ * H * (resolvent B ζ)^2

/-- Ordered second insertion difference of the squared resolvent. The two
directions occur in the displayed order, with four resolvent factors.-/
def resolventSquareSecondDifference (ζ : ℂ) (A B C H K : Matrix n n ℂ) : Matrix n n ℂ :=
  (resolvent A ζ)^2 * H * resolvent B ζ * K * resolvent C ζ +
    resolvent A ζ * H * (resolvent B ζ)^2 * K * resolvent C ζ +
    resolvent A ζ * H * resolvent B ζ * K * (resolvent C ζ)^2

/-- The scalar rational expression `1/(ζ-x)` evaluates to the native resolvent.
@isnad1 id=eq.0h3v.s7.6d24d295b351 from=translated src=- shape=ab80f816 vocab=7661af27
-/
theorem rationalMatrixEval_resolvent (ζ : ℂ) (A : Matrix n n ℂ) :
    rationalMatrixEval 1 (C ζ-X) A = resolvent A ζ := by
  simp [rationalMatrixEval,resolvent_matrix_eq_inv,Algebra.algebraMap_eq_smul_one]

/-- The rational expression `1/(ζ-x)^2` evaluates to the squared resolvent.
@isnad1 id=eq.0h3v.s7.54f1eb15d0c1 from=translated src=- shape=ea1cb26d vocab=882bb9ff
-/
theorem rationalMatrixEval_resolvent_sq (ζ : ℂ) (A : Matrix n n ℂ) :
    rationalMatrixEval 1 ((C ζ-X)^2) A = (resolvent A ζ)^2 := by
  calc
    rationalMatrixEval 1 ((C ζ-X)^2) A =
        rationalMatrixEval 1 (C ζ-X) A * rationalMatrixEval 1 (C ζ-X) A := by
      simpa only [one_mul,pow_two] using
        rationalMatrixEval_mul (1 : ℂ[X]) (C ζ-X) 1 (C ζ-X) A
    _ = resolvent A ζ * resolvent A ζ := by rw [rationalMatrixEval_resolvent ζ A]
    _ = (resolvent A ζ)^2 := (pow_two _).symm

/-- First rational block differences of the resolvent are its usual ordered
single-direction insertion.
@isnad1 id=eq.0h5v.s7.e5b5190b1d79 from=translated src=- shape=44c03815 vocab=aec1dab6
-/
theorem rationalBlockDifference_resolvent (ζ : ℂ) (A B H : Matrix n n ℂ) :
    rationalBlockDifference 1 (C ζ-X) A B H = resolvent A ζ * H * resolvent B ζ := by
  simp [rationalBlockDifference_one,polynomialBlockDifference_sub,
    resolvent_matrix_eq_inv,Algebra.algebraMap_eq_smul_one]

private theorem isUnit_aeval_shift {A : Matrix n n ℂ} (hA : A.IsHermitian)
    {ζ : ℂ} (hζ : ζ.im ≠ 0) : IsUnit (aeval A (C ζ-X)) := by
  simpa only [map_sub,aeval_C,aeval_X,Algebra.algebraMap_eq_smul_one] using
    hA.isUnit_smul_one_sub_of_im_ne_zero hζ

/-- The explicit first squared-resolvent difference is exactly the corresponding
rational block difference on its Hermitian nonreal domain.
@isnad1 id=eq.3h5v.s7.273c60987e07 from=translated src=- shape=3833ccf7 vocab=29db2e4b
-/
theorem rationalBlockDifference_resolvent_sq (ζ : ℂ) (A B H : Matrix n n ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hζ : ζ.im ≠ 0) :
    rationalBlockDifference 1 ((C ζ-X)^2) A B H = resolventSquareDifference ζ A B H := by
  have hQA := isUnit_aeval_shift hA hζ
  have hQB := isUnit_aeval_shift hB hζ
  have h := rationalBlockDifference_mul (1 : ℂ[X]) (C ζ-X) 1 (C ζ-X) A B H
    hQA hQB hQA hQB
  simp only [one_mul,←pow_two,one_pow,rationalMatrixEval_resolvent,rationalBlockDifference_resolvent] at h
  rw [h]
  unfold resolventSquareDifference
  noncomm_ring

/-- The explicit ordered second squared-resolvent difference is the corresponding
second rational block difference, with both directions in their original order.
@isnad1 id=eq.4h7v.s8.ab695aad8a9f from=translated src=- shape=15bddd34 vocab=6d464ede
-/
theorem rationalSecondBlockDifference_resolvent_sq (ζ : ℂ) (A B C H K : Matrix n n ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian) (hζ : ζ.im ≠ 0) :
    rationalSecondBlockDifference 1 ((Polynomial.C ζ-X)^2) A B C H K =
      resolventSquareSecondDifference ζ A B C H K := by
  have hQA := isUnit_aeval_shift hA hζ
  have hQB := isUnit_aeval_shift hB hζ
  have hQC := isUnit_aeval_shift hC hζ
  have h := rationalSecondBlockDifference_mul (1 : ℂ[X]) (Polynomial.C ζ-X) 1
    (Polynomial.C ζ-X) A B C H K hQA hQB hQC hQA hQB hQC
  simp only [one_mul,←pow_two,one_pow,rationalMatrixEval_resolvent,rationalBlockDifference_resolvent,
    rationalSecondBlockDifference_resolvent,←resolvent_matrix_eq_inv] at h
  rw [h]
  unfold resolventSquareSecondDifference
  noncomm_ring

/-- The squared resolvent's exact increment is its first insertion difference.
Source: supplied Cauchy-transform reroute, (comparison-L).
@isnad1 id=eq.3h4v.s8.b071e6d42456 from=translated src=- shape=b855d889 vocab=7cced6a5
-/
theorem resolvent_sq_sub_resolvent_sq (ζ : ℂ) (A B : Matrix n n ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hζ : ζ.im ≠ 0) :
    (resolvent A ζ)^2-(resolvent B ζ)^2 = resolventSquareDifference ζ A B (A-B) := by
  have h := rationalMatrixEval_sub 1 ((C ζ-X)^2) A B
    (by simpa only [map_pow] using (isUnit_aeval_shift hA hζ).pow 2)
    (by simpa only [map_pow] using (isUnit_aeval_shift hB hζ).pow 2)
  simpa only [rationalMatrixEval_resolvent_sq,
    rationalBlockDifference_resolvent_sq ζ A B (A-B) hA hB hζ] using h

/-- The first insertion minus the derivative at a third base point is the
sum of the two ordered second differences. Source: supplied reroute (comparison-T).
@isnad1 id=eq.4h6v.s8.1ccd17b965ee from=translated src=- shape=6ef52fd2 vocab=925ea73e
-/
theorem resolventSquareDifference_sub_self (ζ : ℂ) (A B C H : Matrix n n ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian) (hζ : ζ.im ≠ 0) :
    resolventSquareDifference ζ A B H-resolventSquareDifference ζ C C H =
      resolventSquareSecondDifference ζ A B C H (B-C) +
        resolventSquareSecondDifference ζ A C C (A-C) H := by
  have hQA : IsUnit (aeval A ((Polynomial.C ζ-X)^2)) := by
    simpa only [map_pow] using (isUnit_aeval_shift hA hζ).pow 2
  have hQB : IsUnit (aeval B ((Polynomial.C ζ-X)^2)) := by
    simpa only [map_pow] using (isUnit_aeval_shift hB hζ).pow 2
  have hQC : IsUnit (aeval C ((Polynomial.C ζ-X)^2)) := by
    simpa only [map_pow] using (isUnit_aeval_shift hC hζ).pow 2
  have hr := rationalBlockDifference_sub_right 1 ((Polynomial.C ζ-X)^2) A B C H hQA hQB hQC
  have hl := rationalBlockDifference_sub_left 1 ((Polynomial.C ζ-X)^2) A C C H hQA hQC hQC
  simp only [rationalBlockDifference_resolvent_sq ζ _ _ _ hA hB hζ,
    rationalBlockDifference_resolvent_sq ζ _ _ _ hA hC hζ,
    rationalBlockDifference_resolvent_sq ζ _ _ _ hC hC hζ,
    rationalSecondBlockDifference_resolvent_sq ζ _ _ _ _ _ hA hB hC hζ,
    rationalSecondBlockDifference_resolvent_sq ζ _ _ _ _ _ hA hC hC hζ] at hr hl
  rw [←hr,←hl]
  abel

/-- The first squared-resolvent insertion is real-linear in its direction.
@isnad1 id=eq.0h6v.s7.502c6557d4cf from=translated src=- shape=a919f985 vocab=e6a1ac96
-/
theorem resolventSquareDifference_smul (ζ : ℂ) (A B H : Matrix n n ℂ) (a : ℝ) :
    resolventSquareDifference ζ A B (a • H) = a • resolventSquareDifference ζ A B H := by
  simp only [resolventSquareDifference,Matrix.mul_smul,Matrix.smul_mul,smul_add]

/-- The ordered second insertion is real-linear in its first direction.
@isnad1 id=eq.0h8v.s7.b9083b608b6a from=translated src=- shape=b9856d1c vocab=9c4d1208
-/
theorem resolventSquareSecondDifference_smul_left (ζ : ℂ) (A B C H K : Matrix n n ℂ) (a : ℝ) :
    resolventSquareSecondDifference ζ A B C (a • H) K =
      a • resolventSquareSecondDifference ζ A B C H K := by
  simp only [resolventSquareSecondDifference,Matrix.mul_smul,Matrix.smul_mul,smul_add]

/-- The ordered second insertion is real-linear in its second direction.
@isnad1 id=eq.0h8v.s7.98cdd8a7ae04 from=translated src=- shape=025dc8d3 vocab=9c4d1208
-/
theorem resolventSquareSecondDifference_smul_right (ζ : ℂ) (A B C H K : Matrix n n ℂ) (a : ℝ) :
    resolventSquareSecondDifference ζ A B C H (a • K) =
      a • resolventSquareSecondDifference ζ A B C H K := by
  simp only [resolventSquareSecondDifference,Matrix.mul_smul,Matrix.smul_mul,smul_add]

/-- An affine increment extracts its actual scalar coefficient from the first
squared-resolvent difference.
@isnad1 id=eq.4h6v.s8.95d267a55dec from=translated src=- shape=2b3dd65f vocab=f8675853
-/
theorem resolvent_sq_sub_resolvent_sq_of_sub_eq_smul
    (ζ : ℂ) (A B H : Matrix n n ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hζ : ζ.im ≠ 0) (a : ℝ) (hAB : A-B = a • H) :
    (resolvent A ζ)^2-(resolvent B ζ)^2 = a • resolventSquareDifference ζ A B H := by
  rw [resolvent_sq_sub_resolvent_sq ζ A B hA hB hζ,hAB,resolventSquareDifference_smul]

/-- Exact ordered second remainder for affine base-point increments. No
commutation or mixed-Hessian symmetrization is used.
Source: the supplied Cauchy-transform reroute (comparison-T).
atlas: cauchy-transform-gaussian-universality (partial)
@isnad1 id=eq.6h9v.s8.e2a5c0cff593 from=translated src=- shape=2bba680d vocab=63b3a01e
-/
theorem resolventSquareDifference_sub_self_of_sub_eq_smul
    (ζ : ℂ) (A B C H E F : Matrix n n ℂ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hC : C.IsHermitian) (hζ : ζ.im ≠ 0)
    (a : ℝ) (hBC : B-C = a • E) (hAC : A-C = a • F) :
    resolventSquareDifference ζ A B H - resolventSquareDifference ζ C C H =
      a • (resolventSquareSecondDifference ζ A B C H E +
        resolventSquareSecondDifference ζ A C C F H) := by
  rw [resolventSquareDifference_sub_self ζ A B C H hA hB hC hζ,hBC,hAC,
    resolventSquareSecondDifference_smul_left,resolventSquareSecondDifference_smul_right,smul_add]

end NLAlib
