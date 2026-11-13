import Tengoku.Nlalib.NLAlib.Matrix.Functions.RationalBlocks
import Tengoku.Nlalib.NLAlib.ForMathlib.LinearAlgebra.MatrixBicommutant

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Product, inverse and resolvent block rules

Actual triangular evaluations give the product and inverse insertion rules,
and in particular the ordered second resolvent difference. Source: F16--F19.
-/

noncomputable section
open Polynomial
open scoped Matrix
namespace NLAlib
variable {𝕜 n : Type*} [Field 𝕜] [Fintype n] [DecidableEq n]

/--
@isnad1 id=eq.0h6v.s7.4ce72facf953 from=translated src=- shape=bb1937ad vocab=4d7a54e7
-/
@[simp] theorem polynomialBlockDifference_C (c : 𝕜) (A B H : Matrix n n 𝕜) :
    polynomialBlockDifference (C c) A B H = 0 := by
  simp [polynomialBlockDifference, monomialBlockDifference]

/--
@isnad1 id=eq.0h8v.s7.a82f126d86f2 from=translated src=- shape=e7efa4c9 vocab=30fc0acc
-/
@[simp] theorem polynomialSecondBlockDifference_C (c : 𝕜) (A B D G H : Matrix n n 𝕜) :
    polynomialSecondBlockDifference (C c) A B D G H = 0 := by
  simp [polynomialSecondBlockDifference]

/--
@isnad1 id=eq.0h5v.s6.978b6f7a679e from=translated src=- shape=903da860 vocab=f55b7afa
-/
@[simp] theorem polynomialBlockDifference_one (A B H : Matrix n n 𝕜) :
    polynomialBlockDifference 1 A B H = 0 := polynomialBlockDifference_C 1 A B H

/--
@isnad1 id=eq.0h7v.s6.d25403288adf from=translated src=- shape=60062c25 vocab=73640754
-/
@[simp] theorem polynomialSecondBlockDifference_one (A B C G H : Matrix n n 𝕜) :
    polynomialSecondBlockDifference 1 A B C G H = 0 :=
  polynomialSecondBlockDifference_C 1 A B C G H

/--
@isnad1 id=eq.0h5v.s5.fa783dc9d970 from=translated src=- shape=1d1b103f vocab=23fb5b5d
-/
@[simp] theorem polynomialBlockDifference_X (A B H : Matrix n n 𝕜) :
    polynomialBlockDifference X A B H = H := by
  simp [polynomialBlockDifference, monomialBlockDifference, Finset.sum_range_succ]

/--
@isnad1 id=eq.0h7v.s6.4af4802fb5e9 from=translated src=- shape=1699f399 vocab=ed4537bc
-/
@[simp] theorem polynomialSecondBlockDifference_X (A B C G H : Matrix n n 𝕜) :
    polynomialSecondBlockDifference X A B C G H = 0 := by
  simp [polynomialSecondBlockDifference, monomialBlockDifference, Finset.sum_range_succ]

/--
@isnad1 id=eq.0h7v.s7.0e2db65a5e9b from=translated src=- shape=6d97b59f vocab=2863b5cb
-/
theorem polynomialBlockDifference_sub (P Q : 𝕜[X]) (A B H : Matrix n n 𝕜) :
    polynomialBlockDifference (P - Q) A B H =
      polynomialBlockDifference P A B H - polynomialBlockDifference Q A B H := by
  ext i j
  have h := congrArg (fun D : Matrix (n ⊕ n) (n ⊕ n) 𝕜 => D (Sum.inl i) (Sum.inr j))
    (map_sub (aeval (upperBlockTwo A H B)) P Q)
  simpa only [aeval_upperBlockTwo, Matrix.sub_apply, Matrix.fromBlocks_apply₁₂] using h

/--
@isnad1 id=eq.0h9v.s7.80faf239e593 from=translated src=- shape=2009c10a vocab=21ad2e4c
-/
theorem polynomialSecondBlockDifference_sub (P Q : 𝕜[X]) (A B C G H : Matrix n n 𝕜) :
    polynomialSecondBlockDifference (P - Q) A B C G H =
      polynomialSecondBlockDifference P A B C G H - polynomialSecondBlockDifference Q A B C G H := by
  ext i j
  have h := congrArg (fun D : Matrix ((n ⊕ n) ⊕ n) ((n ⊕ n) ⊕ n) 𝕜 =>
    D (Sum.inl (Sum.inl i)) (Sum.inr j)) (map_sub (aeval (upperBlockThree A G B H C)) P Q)
  simpa only [aeval_upperBlockThree, Matrix.sub_apply, Matrix.fromBlocks_apply₁₂,
    Matrix.fromRows_apply_inl] using h

/-- Rational evaluation respects multiplication of scalar rational expressions.
@isnad1 id=eq.0h7v.s7.f35b9f917905 from=translated src=- shape=07ffd16f vocab=e36790f0
-/
theorem rationalMatrixEval_mul (P Q R S : 𝕜[X]) (A : Matrix n n 𝕜) :
    rationalMatrixEval (P * R) (Q * S) A =
      rationalMatrixEval P Q A * rationalMatrixEval R S A := by
  have hc : Commute (aeval A R) (aeval A Q)⁻¹ :=
    ((Commute.all R Q).map (aeval A).toRingHom).matrix_inv_right
  rw [show Q * S = S * Q from mul_comm Q S]
  simp only [rationalMatrixEval, map_mul, Matrix.mul_inv_rev]
  calc
    _ = aeval A P * (aeval A R * (aeval A Q)⁻¹) * (aeval A S)⁻¹ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hc.eq]; simp only [Matrix.mul_assoc]

/-- First block product rule, proved by multiplication of the actual evaluated blocks.
Source: F16.
atlas: matrix-function-block-divided-differences (partial)
@isnad1 id=eq.4h9v.s10.8e671cec3e83 from=translated src=- shape=869abf83 vocab=579e6501
-/
theorem rationalBlockDifference_mul (P Q R S : 𝕜[X]) (A B H : Matrix n n 𝕜)
    (hQA : IsUnit (aeval A Q)) (hQB : IsUnit (aeval B Q))
    (hSA : IsUnit (aeval A S)) (hSB : IsUnit (aeval B S)) :
    rationalBlockDifference (P * R) (Q * S) A B H =
      rationalMatrixEval P Q A * rationalBlockDifference R S A B H +
        rationalBlockDifference P Q A B H * rationalMatrixEval R S B := by
  have h := rationalMatrixEval_mul P Q R S (upperBlockTwo A H B)
  rw [rationalMatrixEval_upperBlockTwo P Q A B H hQA hQB,
    rationalMatrixEval_upperBlockTwo R S A B H hSA hSB,
    rationalMatrixEval_upperBlockTwo (P * R) (Q * S) A B H
      (by simpa only [map_mul] using hQA.mul hSA) (by simpa only [map_mul] using hQB.mul hSB),
    Matrix.fromBlocks_multiply] at h
  exact congrArg Matrix.toBlocks₁₂ h

/-- Ordered second block product rule, including the cross insertion in its
specified order. Source: F16.
atlas: matrix-function-block-divided-differences (partial)
@isnad1 id=eq.6h11v.s11.4f016fb76a71 from=translated src=- shape=08f16337 vocab=1039198b
-/
theorem rationalSecondBlockDifference_mul (P Q R S : 𝕜[X]) (A B C G H : Matrix n n 𝕜)
    (hQA : IsUnit (aeval A Q)) (hQB : IsUnit (aeval B Q)) (hQC : IsUnit (aeval C Q))
    (hSA : IsUnit (aeval A S)) (hSB : IsUnit (aeval B S)) (hSC : IsUnit (aeval C S)) :
    rationalSecondBlockDifference (P * R) (Q * S) A B C G H =
      rationalMatrixEval P Q A * rationalSecondBlockDifference R S A B C G H +
      rationalBlockDifference P Q A B G * rationalBlockDifference R S B C H +
      rationalSecondBlockDifference P Q A B C G H * rationalMatrixEval R S C := by
  have h := rationalMatrixEval_mul P Q R S (upperBlockThree A G B H C)
  rw [rationalMatrixEval_upperBlockThree P Q A B C G H hQA hQB hQC,
    rationalMatrixEval_upperBlockThree R S A B C G H hSA hSB hSC,
    rationalMatrixEval_upperBlockThree (P * R) (Q * S) A B C G H
      (by simpa only [map_mul] using hQA.mul hSA) (by simpa only [map_mul] using hQB.mul hSB)
      (by simpa only [map_mul] using hQC.mul hSC), Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul] at h
  ext i j
  have he := congrArg (fun D => D (Sum.inl (Sum.inl i)) (Sum.inr j)) h
  simpa using he

/-- First block inverse rule. Source: F17.
@isnad1 id=eq.0h6v.s9.c9d10ace2caa from=translated src=- shape=696bbfc2 vocab=f7db8856
-/
theorem rationalBlockDifference_one (Q : 𝕜[X]) (A B H : Matrix n n 𝕜) :
    rationalBlockDifference 1 Q A B H =
      -((aeval A Q)⁻¹ * polynomialBlockDifference Q A B H * (aeval B Q)⁻¹) := by
  simp [rationalBlockDifference, rationalMatrixEval,
    Matrix.mul_assoc]

/-- Ordered second inverse rule. Source: F17.
atlas: matrix-function-block-divided-differences (partial)
@isnad1 id=eq.0h8v.s10.2c92ef0968a9 from=translated src=- shape=da7cfd2d vocab=d5a32174
-/
theorem rationalSecondBlockDifference_one (Q : 𝕜[X]) (A B C G H : Matrix n n 𝕜) :
    rationalSecondBlockDifference 1 Q A B C G H =
      (aeval A Q)⁻¹ * polynomialBlockDifference Q A B G * (aeval B Q)⁻¹ *
        polynomialBlockDifference Q B C H * (aeval C Q)⁻¹ -
      (aeval A Q)⁻¹ * polynomialSecondBlockDifference Q A B C G H * (aeval C Q)⁻¹ := by
  simp [rationalSecondBlockDifference, rationalBlockDifference_one, rationalMatrixEval,
    Matrix.add_mul, Matrix.mul_assoc]
  abel

/-- The ordered second resolvent difference contains precisely one insertion
of each direction in its prescribed order. Source: F19.
atlas: matrix-function-block-divided-differences (partial)
@isnad1 id=eq.0h8v.s9.9406d171e471 from=translated src=- shape=e3aa5b1d vocab=5454730d
-/
theorem rationalSecondBlockDifference_resolvent (ζ : 𝕜) (A B C G H : Matrix n n 𝕜) :
    rationalSecondBlockDifference 1 (Polynomial.C ζ - X) A B C G H =
      (ζ • (1 : Matrix n n 𝕜) - A)⁻¹ * G * (ζ • (1 : Matrix n n 𝕜) - B)⁻¹ * H *
        (ζ • (1 : Matrix n n 𝕜) - C)⁻¹ := by
  rw [rationalSecondBlockDifference_one]
  simp [polynomialBlockDifference_sub, polynomialSecondBlockDifference_sub,
    Algebra.algebraMap_eq_smul_one]

end NLAlib
