/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Tengoku.JacobianTwo.JacobianTwo.QuadraticDenominator
import Tengoku.JacobianTwo.JacobianTwo.QuadraticDirectPackage

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Unit conclusion after the denominator descent

Once `h ∣ g`, the center and centered residual return to the embedded
polynomial ring.  The constant-coefficient equation of the quadratic
recurrence then shows that `k / h` is a polynomial, forcing `h` to be a unit.
-/

noncomputable section

open scoped Polynomial Polynomial.Bivariate
open Polynomial

namespace JacobianTwo.QuadraticUnitConclusion

open JacobianTwo.FractionRingDerivative
open JacobianTwo.QuadraticDenominator
open JacobianTwo.QuadraticDirectPackage
open JacobianTwo.QuadraticRecurrence
open JacobianTwo.QuadraticReduction
open JacobianTwo.QuadraticSpecialization
open JacobianTwo.VariableLeadingQuadratic

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
/-- The two routes for embedding a scalar into `Frac(K[X])` agree.
@isnad1 id=eq.0h2v.s9.3e5d8dd3b7c2 from=translated src=- shape=abbd2878 vocab=e5feb544
-/
theorem toPolynomialFractionField_C (a : K) :
    toPolynomialFractionField (C a) =
      algebraMap K (FractionRing K[X]) a := by
  calc
    algebraMap K[X] (FractionRing K[X]) (C a) =
        algebraMap K[X] (FractionRing K[X]) (algebraMap K K[X] a) := by
      rw [Polynomial.algebraMap_eq]
    _ = algebraMap K (FractionRing K[X]) a :=
      IsScalarTower.algebraMap_apply K K[X] (FractionRing K[X]) a

/-- If `g = h*s`, cancellation in the fraction field makes the quadratic
center an embedded polynomial.
@isnad1 id=eq.2h4v.s8.03d408a31442 from=translated src=- shape=6ee2184c vocab=2ac71f17
-/
theorem fractionQuadraticCenter_eq_of_eq_mul
    {eps : K} {h s : K[X]} (heps : eps ≠ 0) (hh : h ≠ 0) :
    fractionQuadraticCenter eps h (h * s) =
      toPolynomialFractionField (C ((2 * eps)⁻¹) * s) := by
  have hepsPolynomial : C (2 * eps) ≠ (0 : K[X]) := by
    exact C_ne_zero.mpr (mul_ne_zero two_ne_zero heps)
  have hepsFraction :
      toPolynomialFractionField (C (2 * eps)) ≠ 0 := by
    simpa [toPolynomialFractionField] using
      (IsFractionRing.injective K[X] (FractionRing K[X])).ne hepsPolynomial
  have hhFraction : toPolynomialFractionField h ≠ 0 := by
    simpa [toPolynomialFractionField] using
      (IsFractionRing.injective K[X] (FractionRing K[X])).ne hh
  change
    toPolynomialFractionField (h * s) /
        (2 * toPolynomialFractionField (C eps) *
          toPolynomialFractionField h) =
      toPolynomialFractionField (C ((2 * eps)⁻¹) * s)
  rw [show toPolynomialFractionField (h * s) =
      toPolynomialFractionField h * toPolynomialFractionField s by
        simp [toPolynomialFractionField],
    show toPolynomialFractionField (C ((2 * eps)⁻¹) * s) =
      toPolynomialFractionField (C ((2 * eps)⁻¹)) *
        toPolynomialFractionField s by
          simp [toPolynomialFractionField],
    toPolynomialFractionField_C, toPolynomialFractionField_C, map_inv₀,
    map_mul, map_ofNat]
  field_simp [hhFraction, hepsFraction]

/-- After `g = h*s`, the centered residual is also the image of an explicit
polynomial in `K[X]`.
@isnad1 id=eq.2h5v.s9.43e106e1ee68 from=translated src=- shape=146ad1fd vocab=ae1dc1f7
-/
theorem fractionQuadraticCenteredResidual_eq_of_eq_mul
    {eps : K} {h s f : K[X]} (heps : eps ≠ 0) (hh : h ≠ 0) :
    fractionQuadraticCenteredResidual eps h (h * s) f =
      toPolynomialFractionField
        (f - C eps * (C ((2 * eps)⁻¹) * s) ^ 2) := by
  rw [fractionQuadraticCenteredResidual, quadraticCenteredResidual,
    fractionQuadraticCenter_eq_of_eq_mul heps hh]
  simp [toPolynomialFractionField]

omit [CharZero K] in
/-- Evaluating a constant-field polynomial at an embedded polynomial remains
in the embedded polynomial ring, with composition as an explicit witness.
@isnad1 id=eq.0h3v.s10.92a52e2461ae from=translated src=- shape=618b4b14 vocab=7a5a4afb
-/
theorem aeval_toPolynomialFractionField
    (F₀ S : K[X]) :
    aeval (toPolynomialFractionField F₀) S =
      toPolynomialFractionField (S.comp F₀) := by
  simpa only [eval_map_algebraMap] using
    eval_map_algebraMap_at_toPolynomialFractionField S F₀

omit [CharZero K] in
/-- Fraction-field differentiation preserves the embedded polynomial ring.
@isnad1 id=eq.0h2v.s11.de4e1234dbd8 from=translated src=- shape=17eed951 vocab=86f0c566
-/
theorem fractionRingDerivative_toPolynomialFractionField (p : K[X]) :
    fractionRingDerivative (toPolynomialFractionField p) =
      toPolynomialFractionField (derivative p) := by
  exact fractionRingDerivative_algebraMap p

/-- Once `h ∣ g`, the direct certificate's constant-coefficient recurrence
shows that the transformed Jacobian constant `k/h` belongs to the embedded
polynomial ring.
@isnad1 id=mem.4h11v.s10.fc0242a3023c from=translated src=- shape=2dd31ab8 vocab=180b07d8
-/
theorem fractionCenteredJacobianConstant_mem_base_of_certificate_of_dvd
    {eps k lam : K} {h g f : K[X]} {m : ℕ} {P : K[X][Y]}
    {H B : (FractionRing K[X])[X]}
    (cert : Certificate eps k lam h g f P H B m)
    (heps : eps ≠ 0) (hh : h ≠ 0) (hg : h ∣ g) :
    fractionCenteredJacobianConstant k h ∈
      Set.range (algebraMap K[X] (FractionRing K[X])) := by
  obtain ⟨s, rfl⟩ := hg
  let F₀ : K[X] :=
    f - C eps * (C ((2 * eps)⁻¹) * s) ^ 2
  have hF :
      fractionQuadraticCenteredResidual eps h (h * s) f =
        toPolynomialFractionField F₀ := by
    simpa only [F₀] using
      fractionQuadraticCenteredResidual_eq_of_eq_mul
        (f := f) heps hh
  obtain ⟨S, hcoeff, _hdegree, _hlead⟩ :=
    cert.coefficientWitnesses 0 (Nat.zero_le m)
  have hcoeffPolynomial :
      B.coeff 0 = toPolynomialFractionField (S.comp F₀) := by
    calc
      B.coeff 0 =
          aeval (fractionQuadraticCenteredResidual eps h (h * s) f) S :=
        hcoeff
      _ = aeval (toPolynomialFractionField F₀) S := by rw [hF]
      _ = toPolynomialFractionField (S.comp F₀) :=
        aeval_toPolynomialFractionField F₀ S
  have hconstant :=
    constant_coefficient_equation fractionRingDerivative
      (fractionQuadraticCenteredResidual eps h (h * s) f)
      (fractionCenteredJacobianConstant k h) B cert.recurrence_eq
  refine ⟨-2 * F₀ * derivative (S.comp F₀) -
    derivative F₀ * (S.comp F₀), ?_⟩
  rw [← hconstant, hF, hcoeffPolynomial,
    fractionRingDerivative_toPolynomialFractionField,
    fractionRingDerivative_toPolynomialFractionField]
  simp only [toPolynomialFractionField, map_sub, map_mul, map_neg, map_ofNat]

/-- Step 6: if the denominator descent has established `h ∣ g`, the direct
certificate forces the leading polynomial `h` to be a unit.
@isnad1 id=isunit.5h11v.s9.c8cd66cc9533 from=translated src=- shape=7e62f279 vocab=d61721f4
-/
theorem isUnit_of_certificate_of_dvd
    {eps k lam : K} {h g f : K[X]} {m : ℕ} {P : K[X][Y]}
    {H B : (FractionRing K[X])[X]}
    (cert : Certificate eps k lam h g f P H B m)
    (heps : eps ≠ 0) (hk : k ≠ 0) (hh : h ≠ 0) (hg : h ∣ g) :
    IsUnit h := by
  have hmem :=
    fractionCenteredJacobianConstant_mem_base_of_certificate_of_dvd
      cert heps hh hg
  apply isUnit_polynomial_denominator_of_scalar_fraction_mem_base hh hk
  simpa only [fractionCenteredJacobianConstant,
    toPolynomialFractionField, div_eq_mul_inv] using hmem

end JacobianTwo.QuadraticUnitConclusion
