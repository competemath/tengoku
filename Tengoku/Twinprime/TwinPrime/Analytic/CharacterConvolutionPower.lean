import Tengoku.Twinprime.TwinPrime.Analytic.CharacterConvolutionCancellation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A power bound for three nonprincipal character convolutions

The proved two-thirds-power estimate loses one logarithm. Absorbing that
logarithm into `x^(1/12)` yields an explicit three-quarters-power estimate
for the actual coefficients, including every natural prefix.
-/

noncomputable section

open Finset ArithmeticFunction

namespace TwinPrime.Analytic

theorem one_add_log_le_one_add_inv_mul_rpow (x δ : ℝ) (hx : 1 ≤ x) (hδ : 0 < δ) :
    1 + Real.log x ≤ (1 + 1 / δ) * x ^ δ := by
  have hlog := Real.log_le_rpow_div (by linarith : 0 ≤ x) hδ
  have hp := Real.one_le_rpow hx hδ.le
  calc
    _ ≤ x ^ δ + x ^ δ / δ := add_le_add hp hlog
    _ = _ := by ring

theorem one_add_log_le_thirteen_mul_rpow (x : ℝ) (hx : 1 ≤ x) :
    1 + Real.log x ≤ 13 * x ^ (1 / 12 : ℝ) := by
  simpa only [one_div_one_div, show (1 + 12 : ℝ) = 13 by norm_num] using
    one_add_log_le_one_add_inv_mul_rpow x (1 / 12) hx (by norm_num)

theorem norm_three_character_convolution_summatory_le_power {q : ℕ} [NeZero q]
    (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hχ₃ : χ₃ ≠ 1)
    (x : ℝ) (hx : 1 ≤ x) :
    ‖complexArithmeticSummatory
      (toArithmeticFunction (χ₁ ·) * toArithmeticFunction (χ₂ ·) *
        toArithmeticFunction (χ₃ ·)) x‖ ≤
      130 * (q : ℝ) ^ 2 * x ^ (3 / 4 : ℝ) := by
  have hx0 : 0 < x := by linarith
  apply (norm_three_character_convolution_summatory_le χ₁ χ₂ χ₃ hχ₁ hχ₂ hχ₃ x hx).trans
  calc
    _ ≤ 10 * (q : ℝ) ^ 2 * x ^ (2 / 3 : ℝ) * (13 * x ^ (1 / 12 : ℝ)) :=
      mul_le_mul_of_nonneg_left (one_add_log_le_thirteen_mul_rpow x hx) (by positivity)
    _ = 130 * (q : ℝ) ^ 2 * (x ^ (2 / 3 : ℝ) * x ^ (1 / 12 : ℝ)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hx0]
      norm_num

/-- The coefficient-prefix bound includes `N=0` and directly matches the
hypothesis of the ordered power-tail and continuation theorems.-/
theorem norm_three_character_convolution_prefix_le_power {q : ℕ} [NeZero q]
    (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hχ₃ : χ₃ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Ioc 0 N,
      (toArithmeticFunction (χ₁ ·) * toArithmeticFunction (χ₂ ·) *
        toArithmeticFunction (χ₃ ·)) n‖ ≤
      130 * (q : ℝ) ^ 2 * (N : ℝ) ^ (3 / 4 : ℝ) := by
  by_cases hN : N = 0
  · subst N
    simp [Real.zero_rpow (by norm_num : (3 / 4 : ℝ) ≠ 0)]
  · simpa only [complexArithmeticSummatory_nat] using
      norm_three_character_convolution_summatory_le_power χ₁ χ₂ χ₃ hχ₁ hχ₂ hχ₃ (N : ℝ)
        (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN)

end TwinPrime.Analytic
