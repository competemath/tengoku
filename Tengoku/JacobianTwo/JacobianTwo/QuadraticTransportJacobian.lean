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
Jacobian by the ordinary derivative of the substitution.
@isnad1 id=eq.0h6v.s9.a7a8730ba2da from=translated src=- shape=ff5361fb vocab=f90656f6
-/
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
is the same as embedding the original `x`-derivative.
@isnad1 id=eq.0h2v.s11.3eaf9230b0e7 from=translated src=- shape=5cbcdd6d vocab=7f5a22d7
-/
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
coefficient embedding of their original bivariate Jacobian.
@isnad1 id=eq.0h3v.s8.50a7543e7bfd from=translated src=- shape=05fe87e9 vocab=001ea55c
-/
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
substitution.
@isnad1 id=eq.0h6v.s11.643ef136127c from=translated src=- shape=d6768a3e vocab=606e5d54
-/
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

/-- A constant Keller Jacobian becomes `k / h` in the centered chart.
@isnad1 id=eq.1h7v.s11.5765be529948 from=translated src=- shape=9717ace7 vocab=54ae3eee
-/
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
