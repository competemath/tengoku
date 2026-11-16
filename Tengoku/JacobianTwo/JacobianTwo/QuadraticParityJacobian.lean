/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Tengoku.JacobianTwo.JacobianTwo.QuadraticRecurrence
import Tengoku.JacobianTwo.JacobianTwo.VariableLeadingQuadratic
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Jacobian identities for the quadratic parity decomposition

This file isolates the chain-rule cancellation behind

`P = H(Q) + U * B(Q)`.

The coefficient derivation holds the outer indeterminate `U` fixed.  The
resulting Jacobian with `Q` forgets the derivatives of `H` and `B` with respect
to their argument; only their coefficientwise derivatives survive.
-/

noncomputable section

open Polynomial

namespace JacobianTwo.QuadraticParityJacobian

open JacobianTwo.QuadraticRecurrence
open JacobianTwo.VariableLeadingQuadratic

variable {R L : Type*} [CommRing R] [Field L] [Algebra R L]

/-- The Jacobian formed from coefficientwise differentiation and ordinary
polynomial differentiation in the outer indeterminate.-/
def centeredJacobian (D : Derivation R L L) (P Q : L[X]) : L[X] :=
  coefficientwiseDerivative D P * derivative Q -
    derivative P * coefficientwiseDerivative D Q

@[simp]
theorem coefficientwiseDerivative_X (D : Derivation R L L) :
    coefficientwiseDerivative D (X : L[X]) = 0 := by
  ext j
  simp only [coeff_coefficientwiseDerivative, coeff_X, coeff_zero]
  split_ifs <;> simp

@[simp]
theorem coefficientwiseDerivative_C (D : Derivation R L L) (a : L) :
    coefficientwiseDerivative D (C a) = C (D a) := by
  ext j
  simp only [coeff_coefficientwiseDerivative, coeff_C]
  split_ifs <;> simp

/-- Coefficientwise differentiation obeys the expected chain rule for
polynomial composition.-/
theorem coefficientwiseDerivative_comp (D : Derivation R L L) (H Q : L[X]) :
    coefficientwiseDerivative D (H.comp Q) =
      (coefficientwiseDerivative D H).comp Q +
        (derivative H).comp Q * coefficientwiseDerivative D Q := by
  induction H using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [add_comp, map_add, hp, hq]
      ring
  | monomial n a =>
      simp only [monomial_comp, Derivation.leibniz, derivative_monomial,
        coefficientwiseDerivative]
      simp
      ring

/-- Composing the first entry with the second removes the ordinary chain-rule
part from the Jacobian.-/
theorem centeredJacobian_comp_left (D : Derivation R L L) (H Q : L[X]) :
    centeredJacobian D (H.comp Q) Q =
      (coefficientwiseDerivative D H).comp Q * derivative Q := by
  rw [centeredJacobian, coefficientwiseDerivative_comp, derivative_comp]
  ring

/-- The corresponding cancellation for the odd term `X * B(Q)`.-/
theorem centeredJacobian_X_mul_comp_left
    (D : Derivation R L L) (B Q : L[X]) :
    centeredJacobian D (X * (B.comp Q)) Q =
      X * ((coefficientwiseDerivative D B).comp Q) * derivative Q -
        (B.comp Q) * coefficientwiseDerivative D Q := by
  rw [centeredJacobian, Derivation.leibniz, coefficientwiseDerivative_comp,
    derivative_mul, derivative_comp]
  simp only [coefficientwiseDerivative_X, derivative_X]
  ring

/-- The full parity decomposition identity before specializing the centered
quadratic.-/
theorem centeredJacobian_parity_decomposition
    (D : Derivation R L L) (H B Q : L[X]) :
    centeredJacobian D (H.comp Q + X * (B.comp Q)) Q =
      (coefficientwiseDerivative D H).comp Q * derivative Q +
        X * ((coefficientwiseDerivative D B).comp Q) * derivative Q -
        (B.comp Q) * coefficientwiseDerivative D Q := by
  rw [centeredJacobian, map_add, derivative_add,
    coefficientwiseDerivative_comp, derivative_comp,
    Derivation.leibniz, coefficientwiseDerivative_comp, derivative_mul,
    derivative_comp]
  simp only [coefficientwiseDerivative_X, derivative_X]
  ring

/-- For `Q = eps*U^2+F`, the parity identity has one odd summand and one even
summand.  This is the exact algebraic equation used before coefficient
extraction.-/
theorem centeredJacobian_parityQuadratic
    (D : Derivation R L L) (H B : L[X]) (eps F : L)
    (hepsConstant : D eps = 0) :
    centeredJacobian D
        (H.comp (parityQuadratic eps F) +
          X * (B.comp (parityQuadratic eps F)))
        (parityQuadratic eps F) =
      C (2 * eps) * X *
          ((coefficientwiseDerivative D H).comp (parityQuadratic eps F)) +
        C 2 * (parityQuadratic eps F - C F) *
          ((coefficientwiseDerivative D B).comp (parityQuadratic eps F)) -
        C (D F) * (B.comp (parityQuadratic eps F)) := by
  rw [centeredJacobian_parity_decomposition]
  simp only [parityQuadratic, derivative_mul, derivative_C,
    derivative_X, derivative_pow, map_add, Derivation.leibniz,
    coefficientwiseDerivative]
  simp [hepsConstant]
  ring

end JacobianTwo.QuadraticParityJacobian
