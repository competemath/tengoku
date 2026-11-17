/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Tengoku.JacobianTwo.JacobianTwo.QuadraticRecurrencePrimitive
import Tengoku.JacobianTwo.JacobianTwo.QuadraticSpecialization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Direct package for a variable-leading quadratic Keller coordinate

This module composes the centered Jacobian transport, parity extraction,
odd-degree control, recurrence descent, and specialization at the center.  Its
main certificate records every fraction-field conclusion needed before the
remaining denominator argument.
-/

noncomputable section

open scoped Polynomial Polynomial.Bivariate
open Polynomial

namespace JacobianTwo.QuadraticDirectPackage

open JacobianTwo.AffineCoordinate
open JacobianTwo.FractionRingDerivative
open JacobianTwo.QuadraticParityExtraction
open JacobianTwo.QuadraticRecurrence
open JacobianTwo.QuadraticRecurrencePrimitive
open JacobianTwo.QuadraticReduction
open JacobianTwo.QuadraticSpecialization
open JacobianTwo.VariableLeadingQuadratic

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
/-- A nonzero scalar numerator and a nonzero polynomial denominator give a
nonzero transformed Jacobian constant.
@isnad1 id=ne.2h3v.s8.9ea8725f05c0 from=translated src=- shape=3b465ace vocab=16ea6267
-/
theorem fractionCenteredJacobianConstant_ne_zero
    {k : K} {h : K[X]} (hk : k ≠ 0) (hh : h ≠ 0) :
    fractionCenteredJacobianConstant k h ≠ 0 := by
  apply mul_ne_zero
  · simpa [fractionCenteredJacobianConstant, toPolynomialFractionField] using
      (IsFractionRing.injective K[X] (FractionRing K[X])).ne
        (C_ne_zero.mpr hk)
  · exact inv_ne_zero (by
      simpa [fractionCenteredJacobianConstant, toPolynomialFractionField] using
        (IsFractionRing.injective K[X] (FractionRing K[X])).ne hh)

/-- The Keller equation and a parity representation imply the constant-field
condition for the even part and the exact quadratic recurrence for the odd
part.
@isnad1 id=and.4h9v.s12.11ceb2d826b7 from=translated src=- shape=f16010a9 vocab=3f69908a
-/
theorem recurrence_of_keller_parityRepresentation
    {eps k : K} {h g f : K[X]} (P : K[X][Y])
    (H B : (FractionRing K[X])[X])
    (heps : eps ≠ 0) (hh : h ≠ 0)
    (hjac : jacobian P
      (variableQuadraticCoordinate (C eps * h ^ 2) g f) = CC k)
    (hrepr : fractionAffineTransport eps h g P =
      H.comp (fractionCenteredQuadratic eps h g f) +
        X * (B.comp (fractionCenteredQuadratic eps h g f))) :
    coefficientwiseDerivative fractionRingDerivative H = 0 ∧
      recurrencePolynomial fractionRingDerivative
          (fractionQuadraticCenteredResidual eps h g f) B =
        C (fractionCenteredJacobianConstant k h) := by
  have hepsFraction : toPolynomialFractionField (C eps) ≠ 0 := by
    simpa [toPolynomialFractionField] using
      (IsFractionRing.injective K[X] (FractionRing K[X])).ne
        (C_ne_zero.mpr heps)
  have hepsConstant :
      fractionRingDerivative (toPolynomialFractionField (C eps)) = 0 := by
    rw [toPolynomialFractionField, fractionRingDerivative_algebraMap]
    simp
  have hcentered :=
    centeredJacobian_eq_of_jacobian_eq_of_fractionAffineTransport_eq
      P H B heps hh hjac hrepr
  exact coefficientwiseDerivative_eq_zero_and_recurrence_of_centeredJacobian_eq_C
    fractionRingDerivative H B
      (toPolynomialFractionField (C eps))
      (fractionQuadraticCenteredResidual eps h g f)
      (fractionCenteredJacobianConstant k h)
      hepsFraction hepsConstant (by
        simpa only [fractionCenteredQuadratic] using hcentered)

omit [CharZero K] in
/-- Odd degree and the prescribed leading-coefficient shape determine the
degree, nonvanishing, and leading coefficient of the odd parity component.
@isnad1 id=and.6h10v.s12.34592e8f36a1 from=translated src=- shape=93da547e vocab=f13a82dd
-/
theorem odd_part_control_of_parityRepresentation
    {eps lam : K} {h g f : K[X]} {m : ℕ} (P : K[X][Y])
    (H B : (FractionRing K[X])[X])
    (heps : eps ≠ 0) (hlam : lam ≠ 0) (hh : h ≠ 0)
    (hdegree : P.natDegree = 2 * m + 1)
    (hlead : P.leadingCoeff = C lam * h ^ P.natDegree)
    (hrepr : fractionAffineTransport eps h g P =
      H.comp (fractionCenteredQuadratic eps h g f) +
        X * (B.comp (fractionCenteredQuadratic eps h g f))) :
    B.natDegree = m ∧ B ≠ 0 ∧
      B.leadingCoeff =
        toPolynomialFractionField (C lam) /
          toPolynomialFractionField (C eps) ^ m := by
  have hepsFraction : toPolynomialFractionField (C eps) ≠ 0 := by
    simpa [toPolynomialFractionField] using
      (IsFractionRing.injective K[X] (FractionRing K[X])).ne
        (C_ne_zero.mpr heps)
  have hlamFraction : toPolynomialFractionField (C lam) ≠ 0 := by
    simpa [toPolynomialFractionField] using
      (IsFractionRing.injective K[X] (FractionRing K[X])).ne
        (C_ne_zero.mpr hlam)
  have htransportDegree :
      (fractionAffineTransport eps h g P).natDegree = 2 * m + 1 := by
    rw [natDegree_fractionAffineTransport eps P hh, hdegree]
  have htransportLead :
      (fractionAffineTransport eps h g P).leadingCoeff =
        toPolynomialFractionField (C lam) :=
    leadingCoeff_fractionAffineTransport_of_shape eps P hh hlead
  obtain ⟨hBdegree, hBlead⟩ :=
    odd_degree_parityDecomposition_control
      hepsFraction (by
        simpa only [fractionCenteredQuadratic] using hrepr)
      htransportDegree htransportLead
  have hBleadne : B.leadingCoeff ≠ 0 := by
    rw [hBlead]
    exact div_ne_zero hlamFraction (pow_ne_zero m hepsFraction)
  exact ⟨hBdegree, leadingCoeff_ne_zero.mp hBleadne, hBlead⟩

/-- Degree-normalized form of the recurrence descent: after identifying the
odd-part degree with `m`, coefficient `j ≤ m` has a nonzero witness of exact
degree `m-j` in `K[F]`.
@isnad1 id=ex.4h6v.s12.9da28298c00f from=translated src=- shape=af5b6f0a vocab=54a2f9cf
-/
theorem coefficient_witnesses_of_recurrence
    (F C₀ : FractionRing K[X]) (B : (FractionRing K[X])[X])
    {m : ℕ} (hBdegree : B.natDegree = m) (hB : B ≠ 0)
    (hrec : recurrencePolynomial fractionRingDerivative F B = C C₀) :
    ∀ j ≤ m, ∃ S : K[X],
      B.coeff j = aeval F S ∧
      S.natDegree = m - j ∧
      S.leadingCoeff ≠ 0 := by
  intro j hj
  have hjB : j ≤ B.natDegree := by simpa only [hBdegree] using hj
  obtain ⟨S, hcoeff, hdegree, hlead⟩ :=
    coeff_aeval_with_degree_of_fraction_recurrencePolynomial_eq_C
      F C₀ B hB hrec j hjB
  refine ⟨S, hcoeff, ?_, hlead⟩
  simpa only [hBdegree] using hdegree

/-- The complete fraction-field certificate produced before the denominator
descent in the odd-degree variable-leading quadratic case.-/
structure Certificate
    (eps k lam : K) (h g f : K[X]) (P : K[X][Y])
    (H B : (FractionRing K[X])[X]) (m : ℕ) : Prop where
  jacobianConstant_ne : fractionCenteredJacobianConstant k h ≠ 0
  evenDerivative_eq_zero :
    coefficientwiseDerivative fractionRingDerivative H = 0
  recurrence_eq :
    recurrencePolynomial fractionRingDerivative
        (fractionQuadraticCenteredResidual eps h g f) B =
      C (fractionCenteredJacobianConstant k h)
  oddDegree_eq : B.natDegree = m
  odd_ne_zero : B ≠ 0
  oddLeadingCoeff_eq :
    B.leadingCoeff =
      toPolynomialFractionField (C lam) /
        toPolynomialFractionField (C eps) ^ m
  coefficientWitnesses :
    ∀ j ≤ m, ∃ S : K[X],
      B.coeff j =
          aeval (fractionQuadraticCenteredResidual eps h g f) S ∧
        S.natDegree = m - j ∧
        S.leadingCoeff ≠ 0
  centerMulEval_mem_base :
    fractionQuadraticCenter eps h g *
        B.eval (toPolynomialFractionField f) ∈
      Set.range (algebraMap K[X] (FractionRing K[X]))

/-- An odd-degree Keller mate against
`eps*h^2*y^2 + g*y + f`, together with any parity representation of its
fraction-field affine transport, produces the complete direct certificate.
@isnad1 id=certific.8h11v.s11.87142ecde04b from=translated src=- shape=6c29172b vocab=0f88d5fb
-/
theorem certificate_of_odd_degree_keller_parityRepresentation
    {eps k lam : K} {h g f : K[X]} {m : ℕ} (P : K[X][Y])
    (H B : (FractionRing K[X])[X])
    (heps : eps ≠ 0) (hk : k ≠ 0) (hlam : lam ≠ 0) (hh : h ≠ 0)
    (hdegree : P.natDegree = 2 * m + 1)
    (hlead : P.leadingCoeff = C lam * h ^ P.natDegree)
    (hjac : jacobian P
      (variableQuadraticCoordinate (C eps * h ^ 2) g f) = CC k)
    (hrepr : fractionAffineTransport eps h g P =
      H.comp (fractionCenteredQuadratic eps h g f) +
        X * (B.comp (fractionCenteredQuadratic eps h g f))) :
    Certificate eps k lam h g f P H B m := by
  obtain ⟨hH, hrec⟩ :=
    recurrence_of_keller_parityRepresentation
      P H B heps hh hjac hrepr
  obtain ⟨hBdegree, hBne, hBlead⟩ :=
    odd_part_control_of_parityRepresentation
      P H B heps hlam hh hdegree hlead hrepr
  have hwitnesses :=
    coefficient_witnesses_of_recurrence
      (fractionQuadraticCenteredResidual eps h g f)
      (fractionCenteredJacobianConstant k h) B hBdegree hBne hrec
  have hspecialization :=
    center_mul_eval_mem_base_of_fractionAffineTransport_eq_of_derivative_eq_zero
      eps h g f P H B hrepr hH
  exact
    { jacobianConstant_ne :=
        fractionCenteredJacobianConstant_ne_zero hk hh
      evenDerivative_eq_zero := hH
      recurrence_eq := hrec
      oddDegree_eq := hBdegree
      odd_ne_zero := hBne
      oddLeadingCoeff_eq := hBlead
      coefficientWitnesses := hwitnesses
      centerMulEval_mem_base := hspecialization }

end JacobianTwo.QuadraticDirectPackage
