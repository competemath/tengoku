/-
Solution: proofs of the challenge statements, transferred from the
bridge module SalemPisot — the Pisot-number form, and the assemblies of
PdtSalemEndgame (the main construction) and PdtSalemQuadUnit (the
reciprocal quadratic case) re-run there with the index and the family
root kept. The inline Salem block is definitionally
PDT.SalemEndgame.IsSalem; the inline product is definitionally
PDT.SalemCircle.P.
-/
import Tengoku.SalemTheorem.SalemPisot

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms SalemTheorem.salem_theorem` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms SalemTheorem.salem_construction_two_sided` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms SalemTheorem.salem_quadratic_unit` (it only prints; the queue checks the axioms of every declaration). -/

namespace SalemTheorem

open Polynomial

/-- **Salem's theorem** for Pisot numbers: transported through the
pattern data of `minpoly ℤ α`.
@isnad1 id=and.4h2v.s9.0ce81c01e042 from=translated src=- shape=cd58c8dd vocab=a1e3b901
-/
theorem salem_theorem
    (alpha : ℝ) (halpha : 1 < alpha) (hint : IsIntegral ℤ alpha)
    (hpisot : ∀ z ∈ (minpoly ℚ alpha).aroots ℂ, z ≠ (alpha : ℂ) → ‖z‖ < 1)
    (eps : ℝ) (heps : 0 < eps) :
    (∃ tau : ℝ,
      (1 < tau ∧ IsIntegral ℤ tau ∧
        (∀ z : ℂ, (Polynomial.aeval z) (minpoly ℚ tau) = 0 →
          z ≠ (tau : ℂ) → ‖z‖ ≤ 1) ∧
        (∃ z : ℂ, (Polynomial.aeval z) (minpoly ℚ tau) = 0 ∧ ‖z‖ = 1) ∧
        (Polynomial.aeval ((tau : ℂ))⁻¹) (minpoly ℚ tau) = 0) ∧
      alpha - eps < tau ∧ tau < alpha) ∧
    (∃ tau : ℝ,
      (1 < tau ∧ IsIntegral ℤ tau ∧
        (∀ z : ℂ, (Polynomial.aeval z) (minpoly ℚ tau) = 0 →
          z ≠ (tau : ℂ) → ‖z‖ ≤ 1) ∧
        (∃ z : ℂ, (Polynomial.aeval z) (minpoly ℚ tau) = 0 ∧ ‖z‖ = 1) ∧
        (Polynomial.aeval ((tau : ℂ))⁻¹) (minpoly ℚ tau) = 0) ∧
      alpha < tau ∧ tau < alpha + eps) :=
  PDT.SalemPisot.salem_theorem alpha halpha hint hpisot eps heps

/-- **The main construction, with its family root.**
@isnad1 id=ex.7h4v.s10.75e2b382abeb from=translated src=- shape=4eb7620f vocab=fa8b2b1e
-/
theorem salem_construction_two_sided
    (P : Polynomial ℤ) (hmonic : P.Monic)
    (alpha : ℝ) (halpha : 1 < alpha)
    (inside : Multiset ℂ) (hin : ∀ z ∈ inside, ‖z‖ < 1)
    (hconj : inside.map (starRingEnd ℂ) = inside)
    (hfac : P.map (Int.castRingHom ℂ)
      = (X - C (alpha : ℂ)) * (inside.map fun z => X - C z).prod)
    (hnd : (P.map (Int.castRingHom ℝ)).eval alpha⁻¹ ≠ 0)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ e : ℤ, (e = 1 ∨ e = -1) ∧
      0 < (e : ℝ) * (P.map (Int.castRingHom ℝ)).eval alpha⁻¹ ∧
      (∃ m : ℕ, 2 ≤ m ∧ ∃ tau : ℝ,
        (1 < tau ∧ IsIntegral ℤ tau ∧
          (∀ z : ℂ, (Polynomial.aeval z) (minpoly ℚ tau) = 0 →
            z ≠ (tau : ℂ) → ‖z‖ ≤ 1) ∧
          (∃ z : ℂ, (Polynomial.aeval z) (minpoly ℚ tau) = 0 ∧ ‖z‖ = 1) ∧
          (Polynomial.aeval ((tau : ℂ))⁻¹) (minpoly ℚ tau) = 0) ∧
        ((X ^ m * P + C e * P.reverse).map (Int.castRingHom ℝ)).eval tau = 0 ∧
        alpha - eps < tau ∧ tau < alpha) ∧
      (∃ m : ℕ, 2 ≤ m ∧ ∃ tau : ℝ,
        (1 < tau ∧ IsIntegral ℤ tau ∧
          (∀ z : ℂ, (Polynomial.aeval z) (minpoly ℚ tau) = 0 →
            z ≠ (tau : ℂ) → ‖z‖ ≤ 1) ∧
          (∃ z : ℂ, (Polynomial.aeval z) (minpoly ℚ tau) = 0 ∧ ‖z‖ = 1) ∧
          (Polynomial.aeval ((tau : ℂ))⁻¹) (minpoly ℚ tau) = 0) ∧
        ((X ^ m * P - C e * P.reverse).map (Int.castRingHom ℝ)).eval tau = 0 ∧
        alpha < tau ∧ tau < alpha + eps) :=
  PDT.SalemPisot.salem_construction_two_sided P hmonic alpha halpha inside hin hconj
    hfac hnd eps heps

/-- **The reciprocal quadratic case, with its family root.**
@isnad1 id=and.4h3v.s10.f3995e376da9 from=translated src=- shape=3d2016b1 vocab=7231ae15
-/
theorem salem_quadratic_unit
    (r : ℤ) (hr : 3 ≤ r)
    (alpha : ℝ) (halpha : 1 < alpha)
    (hmin : alpha ^ 2 = (r : ℝ) * alpha - 1)
    (eps : ℝ) (heps : 0 < eps) :
    (∃ m : ℕ, 1 ≤ m ∧ ∃ tau : ℝ,
      (1 < tau ∧ IsIntegral ℤ tau ∧
        (∀ z : ℂ, (Polynomial.aeval z) (minpoly ℚ tau) = 0 →
          z ≠ (tau : ℂ) → ‖z‖ ≤ 1) ∧
        (∃ z : ℂ, (Polynomial.aeval z) (minpoly ℚ tau) = 0 ∧ ‖z‖ = 1) ∧
        (Polynomial.aeval ((tau : ℂ))⁻¹) (minpoly ℚ tau) = 0) ∧
      (((X ^ 2 - C r * X + 1) * (X ^ (2 * m) + 1) + X ^ (m + 1) : Polynomial ℤ).map
        (Int.castRingHom ℝ)).eval tau = 0 ∧
      alpha - eps < tau ∧ tau < alpha) ∧
    (∃ m : ℕ, 1 ≤ m ∧ ∃ tau : ℝ,
      (1 < tau ∧ IsIntegral ℤ tau ∧
        (∀ z : ℂ, (Polynomial.aeval z) (minpoly ℚ tau) = 0 →
          z ≠ (tau : ℂ) → ‖z‖ ≤ 1) ∧
        (∃ z : ℂ, (Polynomial.aeval z) (minpoly ℚ tau) = 0 ∧ ‖z‖ = 1) ∧
        (Polynomial.aeval ((tau : ℂ))⁻¹) (minpoly ℚ tau) = 0) ∧
      (((X ^ 2 - C r * X + 1) * (X ^ (2 * m) + 1) - X ^ (m + 1) : Polynomial ℤ).map
        (Int.castRingHom ℝ)).eval tau = 0 ∧
      alpha < tau ∧ tau < alpha + eps) :=
  PDT.SalemPisot.salem_quadratic_unit r hr alpha halpha hmin eps heps

end SalemTheorem

/-! ### Axiom audit — every build prints the audit for the compared theorems -/

