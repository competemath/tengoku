/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Tengoku.JacobianTwo.JacobianTwo.QuadraticParityExtraction
import Tengoku.JacobianTwo.JacobianTwo.QuadraticTransportJacobian
import Tengoku.Seed.Algebra.Polynomial.Eval.Subring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# End-to-end reduction for a variable-leading quadratic coordinate

This module joins the fraction-field affine transport, the transported
Jacobian identity, and parity extraction.  It turns an actual Keller equation
against

`Q = eps * h^2 * y^2 + g * y + f`

into the coefficient recurrence over `Frac(K[x])`, with right-hand side
`k / h`.  It does not yet prove that `h` is a unit; the remaining descent must
use polynomiality of the original first coordinate.

The specialized bridge theorem is kept separate from
`coefficientwiseDerivative_eq_zero_and_recurrence_of_centeredJacobian_eq_C`;
composing those two kernel-checked statements gives the recurrence without a
large monolithic elaboration boundary.
-/

noncomputable section

open scoped Polynomial Polynomial.Bivariate
open Polynomial

namespace JacobianTwo.QuadraticReduction

open JacobianTwo.AffineCoordinate
open JacobianTwo.FractionRingDerivative
open JacobianTwo.QuadraticParityExtraction
open JacobianTwo.QuadraticParityJacobian
open JacobianTwo.QuadraticRecurrence
open JacobianTwo.QuadraticTransportJacobian
open JacobianTwo.VariableLeadingQuadratic

variable {K : Type*} [Field K] [CharZero K]

/-- The centered quadratic in the fraction-field chart.-/
def fractionCenteredQuadratic (eps : K) (h g f : K[X]) :
    (FractionRing K[X])[X] :=
  parityQuadratic (toPolynomialFractionField (C eps))
    (fractionQuadraticCenteredResidual eps h g f)

/-- The transformed constant Jacobian `k / h`.-/
def fractionCenteredJacobianConstant (k : K) (h : K[X]) :
    FractionRing K[X] :=
  toPolynomialFractionField (C k) * (toPolynomialFractionField h)⁻¹

/-- A parity decomposition of the affine transport of an actual Keller pair
satisfies the centered Jacobian equation with right-hand side `k / h`.-/
theorem centeredJacobian_eq_of_jacobian_eq_of_fractionAffineTransport_eq
    {eps k : K} {h g f : K[X]} (P : K[X][Y])
    (H B : (FractionRing K[X])[X])
    (heps : eps ≠ 0) (hh : h ≠ 0)
    (hjac : jacobian P
        (variableQuadraticCoordinate (C eps * h ^ 2) g f) = CC k)
    (hrepr : fractionAffineTransport eps h g P =
      H.comp (fractionCenteredQuadratic eps h g f) +
        X * (B.comp (fractionCenteredQuadratic eps h g f))) :
    centeredJacobian fractionRingDerivative
        (H.comp (fractionCenteredQuadratic eps h g f) +
          X * (B.comp (fractionCenteredQuadratic eps h g f)))
        (fractionCenteredQuadratic eps h g f) =
      C (fractionCenteredJacobianConstant k h) := by
  let epsBar := toPolynomialFractionField (C eps)
  let F := fractionQuadraticCenteredResidual eps h g f
  let q := parityQuadratic epsBar F
  let C₀ := fractionCenteredJacobianConstant k h
  have htransport :=
    centeredJacobian_fractionAffineTransport_of_jacobian_eq
      eps (h := h) (g := g) P
        (variableQuadraticCoordinate (C eps * h ^ 2) g f) hjac
  rw [hrepr,
    map_variableQuadraticCoordinate_comp_fractionCenteredAffineSubstitution
      heps hh] at htransport
  simpa only [fractionCenteredQuadratic, epsBar, F, q, C₀,
    fractionCenteredJacobianConstant] using htransport

/-- If the coefficientwise derivative of a polynomial over `Frac(K[x])`
vanishes, then each coefficient belongs to the constant field `K`.-/
theorem coeff_mem_base_of_coefficientwiseDerivative_eq_zero
    (H : (FractionRing K[X])[X])
    (hH : coefficientwiseDerivative fractionRingDerivative H = 0)
    (j : ℕ) :
    ∃ c : K, H.coeff j = algebraMap K (FractionRing K[X]) c := by
  apply (fractionRingDerivative_eq_zero_iff (H.coeff j)).1
  have hcoeff := congrArg
    (fun S : (FractionRing K[X])[X] ↦ S.coeff j)
    hH
  simpa only [coeff_coefficientwiseDerivative, coeff_zero] using hcoeff

/-- Vanishing coefficientwise derivative assembles to a single polynomial
over the constant field, not merely a coefficient-by-coefficient statement.-/
theorem exists_map_eq_of_coefficientwiseDerivative_eq_zero
    (H : (FractionRing K[X])[X])
    (hH : coefficientwiseDerivative fractionRingDerivative H = 0) :
    ∃ H₀ : K[X],
      H = H₀.map (algebraMap K (FractionRing K[X])) := by
  have hmem :
      H ∈ (mapRingHom (algebraMap K (FractionRing K[X]))).range := by
    rw [mem_map_range]
    intro j
    obtain ⟨c, hc⟩ :=
      coeff_mem_base_of_coefficientwiseDerivative_eq_zero H hH j
    exact ⟨c, hc.symm⟩
  obtain ⟨H₀, hH₀⟩ := hmem
  exact ⟨H₀, hH₀.symm⟩

end JacobianTwo.QuadraticReduction
