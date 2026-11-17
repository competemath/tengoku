/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Tengoku.JacobianTwo.JacobianTwo.QuadraticParityJacobian

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Extracting the two parts of the centered quadratic Jacobian

The centered Jacobian identity splits canonically into a polynomial in
`eps * X ^ 2 + F` and `X` times another such polynomial.  If the Jacobian is
constant, uniqueness of this parity decomposition makes the odd coefficient
vanish and identifies the even coefficient with the quadratic recurrence.
-/

noncomputable section

open Polynomial

namespace JacobianTwo.QuadraticParityExtraction

open JacobianTwo.QuadraticParityJacobian
open JacobianTwo.QuadraticRecurrence
open JacobianTwo.VariableLeadingQuadratic

variable {R L : Type*} [CommRing R] [Field L] [Algebra R L]

/-- A constant has no odd part in the decomposition relative to
`eps * X ^ 2 + F`.
@isnad1 id=and.2h6v.s8.310f831bf89e from=translated src=- shape=c93f835f vocab=e1d82084
-/
theorem parityComponents_eq_constant
    {E A : L[X]} {eps F C₀ : L} (heps : eps ≠ 0)
    (h : E.comp (parityQuadratic eps F) +
        X * (A.comp (parityQuadratic eps F)) = C C₀) :
    E = C C₀ ∧ A = 0 := by
  apply parityDecomposition_unique heps
  simpa using h

/-- If the centered quadratic Jacobian is constant, its odd coefficient is
zero and its even coefficient is exactly the recurrence polynomial.
@isnad1 id=and.3h8v.s9.61257e3f5f47 from=translated src=- shape=73e9d33b vocab=0c9cc530
-/
theorem coefficientwiseDerivative_eq_zero_and_recurrence_of_centeredJacobian_eq_C
    [CharZero L]
    (D : Derivation R L L) (H B : L[X]) (eps F C₀ : L)
    (heps : eps ≠ 0) (hepsConstant : D eps = 0)
    (hjac : centeredJacobian D
        (H.comp (parityQuadratic eps F) +
          X * (B.comp (parityQuadratic eps F)))
        (parityQuadratic eps F) = C C₀) :
    coefficientwiseDerivative D H = 0 ∧
      recurrencePolynomial D F B = C C₀ := by
  have hsplit :
      (recurrencePolynomial D F B).comp (parityQuadratic eps F) +
          X * ((C (2 * eps) * coefficientwiseDerivative D H).comp
            (parityQuadratic eps F)) = C C₀ := by
    rw [centeredJacobian_parityQuadratic D H B eps F hepsConstant] at hjac
    calc
      (recurrencePolynomial D F B).comp (parityQuadratic eps F) +
          X * ((C (2 * eps) * coefficientwiseDerivative D H).comp
            (parityQuadratic eps F)) =
          C (2 * eps) * X *
              ((coefficientwiseDerivative D H).comp
                (parityQuadratic eps F)) +
            C 2 * (parityQuadratic eps F - C F) *
              ((coefficientwiseDerivative D B).comp
                (parityQuadratic eps F)) -
            C (D F) * (B.comp (parityQuadratic eps F)) := by
              simp [recurrencePolynomial]
              ring
      _ = C C₀ := hjac
  obtain ⟨hrecurrence, hodd⟩ := parityComponents_eq_constant heps hsplit
  refine ⟨?_, hrecurrence⟩
  have hscalar : (2 * eps : L) ≠ 0 := mul_ne_zero two_ne_zero heps
  have hCscalar : C (2 * eps) ≠ (0 : L[X]) := C_ne_zero.mpr hscalar
  exact (mul_eq_zero.mp hodd).resolve_left hCscalar

/-- The recurrence package follows directly from a constant centered
quadratic Jacobian.
@isnad1 id=and.3h8v.s10.4e0fec5e7c64 from=translated src=- shape=a8d2054f vocab=cee758a2
-/
theorem recurrence_package_of_centeredJacobian_eq_C
    [CharZero L]
    (D : Derivation R L L) (H B : L[X]) (eps F C₀ : L)
    (heps : eps ≠ 0) (hepsConstant : D eps = 0)
    (hjac : centeredJacobian D
        (H.comp (parityQuadratic eps F) +
          X * (B.comp (parityQuadratic eps F)))
        (parityQuadratic eps F) = C C₀) :
    coefficientwiseDerivative D H = 0 ∧
      D (B.coeff B.natDegree) = 0 ∧
      (∀ j : ℕ, D (B.coeff j) =
        F * D (B.coeff (j + 1)) + (D F / 2) * B.coeff (j + 1)) ∧
      -2 * F * D (B.coeff 0) - D F * B.coeff 0 = C₀ := by
  obtain ⟨hH, hrecurrence⟩ :=
    coefficientwiseDerivative_eq_zero_and_recurrence_of_centeredJacobian_eq_C
      D H B eps F C₀ heps hepsConstant hjac
  exact ⟨hH, recurrence_package D F C₀ B hrecurrence⟩

end JacobianTwo.QuadraticParityExtraction
