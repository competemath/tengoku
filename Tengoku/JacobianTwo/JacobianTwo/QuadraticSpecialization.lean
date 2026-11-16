/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Tengoku.JacobianTwo.JacobianTwo.QuadraticReduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Specialization at the center of the fraction-field chart

Evaluating the inverse affine substitution at its center sends the transported
source variable to zero.  Consequently, the affine transport of a bivariate
polynomial specializes to its constant coefficient in the original source
variable, while the centered quadratic specializes to the embedded original
constant coefficient `f`.
-/

noncomputable section

open scoped Polynomial Polynomial.Bivariate
open Polynomial

namespace JacobianTwo.QuadraticSpecialization

open JacobianTwo.QuadraticReduction
open JacobianTwo.QuadraticRecurrence
open JacobianTwo.FractionRingDerivative
open JacobianTwo.VariableLeadingQuadratic

variable {K : Type*} [Field K]

/-- The inverse affine substitution vanishes at the center of the quadratic.-/
@[simp]
theorem eval_fractionCenteredAffineSubstitution_at_center
    (eps : K) (h g : K[X]) :
    (fractionCenteredAffineSubstitution eps h g).eval
        (fractionQuadraticCenter eps h g) = 0 := by
  simp [fractionCenteredAffineSubstitution, centeredAffineSubstitution]

/-- Specializing an affine transport at the center recovers the embedded
constant coefficient in the original source variable.-/
theorem eval_fractionAffineTransport_at_center
    (eps : K) (h g : K[X]) (P : K[X][Y]) :
    (fractionAffineTransport eps h g P).eval
        (fractionQuadraticCenter eps h g) =
      toPolynomialFractionField (P.coeff 0) := by
  simp [fractionAffineTransport, mapToPolynomialFractionField,
    toPolynomialFractionField, coeff_zero_eq_aeval_zero']

/-- The centered quadratic specializes at its center to the embedded original
constant coefficient `f`.-/
theorem eval_fractionCenteredQuadratic_at_center
    (eps : K) (h g f : K[X]) :
    (fractionCenteredQuadratic eps h g f).eval
        (fractionQuadraticCenter eps h g) =
      toPolynomialFractionField f := by
  simp only [fractionCenteredQuadratic, parityQuadratic, eval_add, eval_mul,
    eval_C, eval_pow, eval_X, fractionQuadraticCenteredResidual,
    quadraticCenteredResidual]
  ring

/-- Evaluating a polynomial with constant-field coefficients at an embedded
polynomial agrees with embedding its polynomial composition.-/
theorem eval_map_algebraMap_at_toPolynomialFractionField
    (H₀ f : K[X]) :
    (H₀.map (algebraMap K (FractionRing K[X]))).eval
        (toPolynomialFractionField f) =
      toPolynomialFractionField (H₀.comp f) := by
  induction H₀ using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.map_add, eval_add, add_comp, hp, hq]
      simp only [toPolynomialFractionField, map_add]
  | monomial n a =>
      have hscalar :
          algebraMap K (FractionRing K[X]) a =
            algebraMap K[X] (FractionRing K[X]) (C a) := by
        calc
          algebraMap K (FractionRing K[X]) a =
              algebraMap K[X] (FractionRing K[X])
                (algebraMap K K[X] a) :=
            (IsScalarTower.algebraMap_apply K K[X]
              (FractionRing K[X]) a).symm
          _ = algebraMap K[X] (FractionRing K[X]) (C a) := by
            rw [Polynomial.algebraMap_eq]
      rw [← C_mul_X_pow_eq_monomial, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_pow, Polynomial.map_X, eval_mul, eval_C, eval_pow,
        eval_X, mul_comp, C_comp, pow_comp, X_comp]
      simp only [toPolynomialFractionField, map_mul, map_pow, hscalar]

/-- If the even part of a parity representation has descended to the constant
field, specializing at the center expresses the odd contribution as an
embedded polynomial exactly.-/
theorem center_mul_eval_eq_of_fractionAffineTransport_eq
    (eps : K) (h g f : K[X]) (P : K[X][Y])
    (H₀ : K[X]) (B : (FractionRing K[X])[X])
    (hrepr : fractionAffineTransport eps h g P =
      (H₀.map (algebraMap K (FractionRing K[X]))).comp
          (fractionCenteredQuadratic eps h g f) +
        X * (B.comp (fractionCenteredQuadratic eps h g f))) :
    fractionQuadraticCenter eps h g *
        B.eval (toPolynomialFractionField f) =
      toPolynomialFractionField (P.coeff 0 - H₀.comp f) := by
  have hspecialized := congrArg
    (fun R : (FractionRing K[X])[X] ↦
      R.eval (fractionQuadraticCenter eps h g)) hrepr
  simp only [eval_fractionAffineTransport_at_center, eval_add, eval_comp,
    eval_mul, eval_X, eval_fractionCenteredQuadratic_at_center,
    eval_map_algebraMap_at_toPolynomialFractionField] at hspecialized
  calc
    fractionQuadraticCenter eps h g *
        B.eval (toPolynomialFractionField f) =
      toPolynomialFractionField (P.coeff 0) -
        toPolynomialFractionField (H₀.comp f) := by
          exact eq_sub_of_add_eq' hspecialized.symm
    _ = toPolynomialFractionField (P.coeff 0 - H₀.comp f) := by
      simp [toPolynomialFractionField]

/-- Set-membership form of
`center_mul_eval_eq_of_fractionAffineTransport_eq`.-/
theorem center_mul_eval_mem_base_of_fractionAffineTransport_eq
    (eps : K) (h g f : K[X]) (P : K[X][Y])
    (H₀ : K[X]) (B : (FractionRing K[X])[X])
    (hrepr : fractionAffineTransport eps h g P =
      (H₀.map (algebraMap K (FractionRing K[X]))).comp
          (fractionCenteredQuadratic eps h g f) +
        X * (B.comp (fractionCenteredQuadratic eps h g f))) :
    fractionQuadraticCenter eps h g *
        B.eval (toPolynomialFractionField f) ∈
      Set.range (algebraMap K[X] (FractionRing K[X])) := by
  refine ⟨P.coeff 0 - H₀.comp f, ?_⟩
  simpa only [toPolynomialFractionField] using
    (center_mul_eval_eq_of_fractionAffineTransport_eq
      eps h g f P H₀ B hrepr).symm

/-- Vanishing of the coefficientwise fraction-field derivative makes the even
part constant-field valued, so specialization forces the odd contribution
back into the embedded polynomial ring.-/
theorem center_mul_eval_mem_base_of_fractionAffineTransport_eq_of_derivative_eq_zero
    [CharZero K]
    (eps : K) (h g f : K[X]) (P : K[X][Y])
    (H B : (FractionRing K[X])[X])
    (hrepr : fractionAffineTransport eps h g P =
      H.comp (fractionCenteredQuadratic eps h g f) +
        X * (B.comp (fractionCenteredQuadratic eps h g f)))
    (hH : coefficientwiseDerivative fractionRingDerivative H = 0) :
    fractionQuadraticCenter eps h g *
        B.eval (toPolynomialFractionField f) ∈
      Set.range (algebraMap K[X] (FractionRing K[X])) := by
  obtain ⟨H₀, hH₀⟩ :=
    exists_map_eq_of_coefficientwiseDerivative_eq_zero H hH
  rw [hH₀] at hrepr
  exact center_mul_eval_mem_base_of_fractionAffineTransport_eq
    eps h g f P H₀ B hrepr

end JacobianTwo.QuadraticSpecialization
