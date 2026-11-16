/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Tengoku.JacobianTwo.JacobianTwo.FractionRingDerivative
import Tengoku.JacobianTwo.JacobianTwo.QuadraticParityJacobian

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Jacobian transport to the centered quadratic chart

This file connects the original bivariate Jacobian over `K[x]` to the
centered Jacobian over `Frac(K[x])[U]`.  Under the inverse affine source
substitution `y = (U - rho) / h`, a constant original Jacobian `k` becomes
the rational function `k / h`.
-/

noncomputable section

open scoped Polynomial Polynomial.Bivariate
open Polynomial

namespace JacobianTwo.QuadraticTransportJacobian

open JacobianTwo.AffineCoordinate
open JacobianTwo.FractionRingDerivative
open JacobianTwo.QuadraticParityJacobian
open JacobianTwo.QuadraticRecurrence
open JacobianTwo.VariableLeadingQuadratic

variable {R L : Type*} [CommRing R] [Field L] [Algebra R L]

/-- Simultaneous substitution in both entries multiplies the centered
Jacobian by the ordinary derivative of the substitution.-/
theorem centeredJacobian_comp (D : Derivation R L L) (P Q T : L[X]) :
    centeredJacobian D (P.comp T) (Q.comp T) =
      (centeredJacobian D P Q).comp T * derivative T := by
  rw [centeredJacobian, coefficientwiseDerivative_comp,
    coefficientwiseDerivative_comp, derivative_comp, derivative_comp,
    centeredJacobian]
  simp only [sub_comp, mul_comp]
  ring

section FractionRing

variable {K : Type*} [Field K]

/-- Applying the fraction-field derivative coefficientwise after embedding
is the same as embedding the original `x`-derivative.-/
theorem coefficientwiseDerivative_mapToPolynomialFractionField
    (P : K[X][Y]) :
    coefficientwiseDerivative fractionRingDerivative
        (mapToPolynomialFractionField P) =
      mapToPolynomialFractionField (xDerivative P) := by
  ext n
  rw [coeff_coefficientwiseDerivative]
  simp only [mapToPolynomialFractionField, coeff_map, coeff_xDerivative]
  exact fractionRingDerivative_algebraMap (P.coeff n)

/-- The centered Jacobian of two coefficient-embedded polynomials is the
coefficient embedding of their original bivariate Jacobian.-/
theorem centeredJacobian_mapToPolynomialFractionField (P Q : K[X][Y]) :
    centeredJacobian fractionRingDerivative
        (mapToPolynomialFractionField P)
        (mapToPolynomialFractionField Q) =
      mapToPolynomialFractionField (jacobian P Q) := by
  rw [centeredJacobian,
    coefficientwiseDerivative_mapToPolynomialFractionField,
    coefficientwiseDerivative_mapToPolynomialFractionField,
    jacobian]
  simp only [mapToPolynomialFractionField, yDerivative_apply,
    derivative_map, Polynomial.map_sub, Polynomial.map_mul]

/-- Exact Jacobian transport through the inverse affine source
substitution.-/
theorem centeredJacobian_fractionAffineTransport
    (eps : K) {h g : K[X]} (P Q : K[X][Y]) :
    centeredJacobian fractionRingDerivative
        (fractionAffineTransport eps h g P)
        (fractionAffineTransport eps h g Q) =
      (mapToPolynomialFractionField (jacobian P Q)).comp
          (fractionCenteredAffineSubstitution eps h g) *
        C (toPolynomialFractionField h)⁻¹ := by
  rw [fractionAffineTransport, fractionAffineTransport,
    centeredJacobian_comp,
    centeredJacobian_mapToPolynomialFractionField,
    fractionCenteredAffineSubstitution,
    derivative_centeredAffineSubstitution]

/-- A constant Keller Jacobian becomes `k / h` in the centered chart.-/
theorem centeredJacobian_fractionAffineTransport_of_jacobian_eq
    (eps : K) {h g : K[X]} (P Q : K[X][Y]) {k : K}
    (hjac : jacobian P Q = CC k) :
    centeredJacobian fractionRingDerivative
        (fractionAffineTransport eps h g P)
        (fractionAffineTransport eps h g Q) =
      C (toPolynomialFractionField (C k) *
        (toPolynomialFractionField h)⁻¹) := by
  rw [centeredJacobian_fractionAffineTransport, hjac]
  simp [mapToPolynomialFractionField, toPolynomialFractionField]

end FractionRing

end JacobianTwo.QuadraticTransportJacobian
