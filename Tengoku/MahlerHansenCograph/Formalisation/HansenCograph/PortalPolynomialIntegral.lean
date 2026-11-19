/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Tengoku.MahlerHansenCograph.Formalisation.HansenCograph.PortalPolynomial
import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Beta

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Integral normalization of portal polynomials

The beta integral cancels the factorial normalization in every Bernstein
basis term.  Consequently the integral of a portal polynomial is its total
coefficient mass divided by the factorial of the Hansen dimension.
-/

open scoped BigOperators

namespace HansenCograph

/-- The beta integral of a pair of natural powers.-/
theorem integral_pow_mul_one_sub_pow (k l : ℕ) :
    (∫ x : ℝ in 0..1, x ^ k * (1 - x) ^ l) =
      (k.factorial : ℝ) * (l.factorial : ℝ) /
        ((k + l + 1).factorial : ℝ) := by
  apply Complex.ofReal_injective
  calc
    ((↑(∫ x : ℝ in 0..1, x ^ k * (1 - x) ^ l) : ℂ)) =
        Complex.betaIntegral ((k + 1 : ℕ) : ℂ) ((l + 1 : ℕ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      simp only [Complex.betaIntegral, Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
        Complex.cpow_natCast, Complex.ofReal_pow, Complex.ofReal_sub,
        Complex.ofReal_one, Complex.ofReal_mul]
    _ = Complex.Gamma ((k + 1 : ℕ) : ℂ) *
          Complex.Gamma ((l + 1 : ℕ) : ℂ) /
          Complex.Gamma (((k + 1 : ℕ) : ℂ) + ((l + 1 : ℕ) : ℂ)) := by
      rw [Complex.betaIntegral_eq_Gamma_mul_div]
      · exact_mod_cast Nat.zero_lt_succ k
      · exact_mod_cast Nat.zero_lt_succ l
    _ = ((k.factorial : ℂ) * (l.factorial : ℂ)) /
          ((k + l + 1).factorial : ℂ) := by
      have hgammaK : Complex.Gamma ((k + 1 : ℕ) : ℂ) =
          (k.factorial : ℂ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          Complex.Gamma_nat_eq_factorial k
      have hgammaL : Complex.Gamma ((l + 1 : ℕ) : ℂ) =
          (l.factorial : ℂ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          Complex.Gamma_nat_eq_factorial l
      have hgamma :
          Complex.Gamma (((k + 1 : ℕ) : ℂ) + ((l + 1 : ℕ) : ℂ)) =
            ((k + l + 1).factorial : ℂ) := by
        rw [show (((k + 1 : ℕ) : ℂ) + ((l + 1 : ℕ) : ℂ)) =
            ((k + l + 1 : ℕ) : ℂ) + 1 by push_cast; ring]
        exact Complex.Gamma_nat_eq_factorial (k + l + 1)
      rw [hgammaK, hgammaL, hgamma]
    _ = ↑((k.factorial : ℝ) * (l.factorial : ℝ) /
          ((k + l + 1).factorial : ℝ)) := by
      apply Complex.ext <;> norm_num

/-- Integrating a portal polynomial sums its portal vector and divides by
the factorial of one more than its degree.-/
theorem integral_portalPolynomial (n : ℕ) (a : ℕ → ℝ) :
    (∫ x : ℝ in 0..1, portalPolynomial n a x) =
      (∑ k ∈ Finset.range (n + 1), a k) /
        ((n + 1).factorial : ℝ) := by
  classical
  unfold portalPolynomial
  rw [intervalIntegral.integral_finsetSum]
  · calc
      (∑ k ∈ Finset.range (n + 1),
        ∫ x : ℝ in 0..1,
          a k / ((k.factorial : ℝ) * ((n - k).factorial : ℝ)) *
            x ^ k * (1 - x) ^ (n - k)) =
        ∑ k ∈ Finset.range (n + 1),
          a k / ((n + 1).factorial : ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        have hsum : k + (n - k) + 1 = n + 1 := by omega
        have hintegrand :
            (fun x : ℝ ↦
              a k / ((k.factorial : ℝ) * ((n - k).factorial : ℝ)) *
                x ^ k * (1 - x) ^ (n - k)) =
              fun x : ℝ ↦
                (a k / ((k.factorial : ℝ) * ((n - k).factorial : ℝ))) *
                  (x ^ k * (1 - x) ^ (n - k)) := by
          funext x
          ring
        rw [hintegrand, intervalIntegral.integral_const_mul,
          integral_pow_mul_one_sub_pow, hsum]
        have hkfac : (k.factorial : ℝ) ≠ 0 := by positivity
        have hnkfac : ((n - k).factorial : ℝ) ≠ 0 := by positivity
        have hnfac : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
        field_simp
      _ = (∑ k ∈ Finset.range (n + 1), a k) /
          ((n + 1).factorial : ℝ) := by
        rw [Finset.sum_div]
  · intro k hk
    exact Continuous.intervalIntegrable (by fun_prop) 0 1

end HansenCograph
