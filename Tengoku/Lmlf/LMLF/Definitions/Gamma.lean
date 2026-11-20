import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The complex Gamma function

LMLF reuses `Complex.Gamma`; it does not define a second Gamma function.  The theorems below make
its Euler integral, convergence domain, real agreement, and totalization at nonpositive integers
available through the definitions API.

This is an identification with the Euler integral only when `0 < s.re`.  It does not assert that
the integral defines Gamma outside that half-plane.
-/

namespace LMLF.Definitions

/-- Euler's integrand for `s` is integrable on the positive real axis when `0 < re s`.-/
theorem gamma_eulerIntegrable {s : ℂ} (hs : 0 < s.re) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ ↦ (Real.exp (-t) : ℂ) * (t : ℂ) ^ (s - 1))
      (Set.Ioi 0) := by
  exact Complex.GammaIntegral_convergent hs

/-- On the half-plane `0 < re s`, Mathlib's complex Gamma function is Euler's integral.-/
theorem gamma_eq_eulerIntegral {s : ℂ} (hs : 0 < s.re) :
    Complex.Gamma s =
      ∫ t in Set.Ioi (0 : ℝ), (Real.exp (-t) : ℂ) * (t : ℂ) ^ (s - 1) := by
  simpa only [Complex.GammaIntegral] using Complex.Gamma_eq_integral hs

/-- Mathlib's complex and real Gamma functions agree on every real input.-/
theorem gamma_ofReal (s : ℝ) :
    Complex.Gamma (s : ℂ) = (Real.Gamma s : ℂ) := by
  exact Complex.Gamma_ofReal s

/-- Mathlib totalizes Gamma to zero at its poles at the nonpositive integers.-/
theorem gamma_neg_nat_eq_zero (n : ℕ) :
    Complex.Gamma (-(n : ℂ)) = 0 := by
  exact Complex.Gamma_neg_nat_eq_zero n

end LMLF.Definitions
