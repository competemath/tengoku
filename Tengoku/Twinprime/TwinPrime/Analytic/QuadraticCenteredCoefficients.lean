import Tengoku.Twinprime.TwinPrime.Analytic.CharacterConvolutionAsymptotic
import Tengoku.Twinprime.TwinPrime.Analytic.QuadraticProductPartialSums

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Residue-subtracted quadratic-product coefficients

Subtracting the actual residue times the constant arithmetic function removes
the linear main term from every natural prefix. The proved summatory estimate
then gives a nine-tenths-power bound, with an explicit logarithm-absorption
constant. The weighted identity is finite and holds for every complex exponent.
-/

noncomputable section

open Finset ArithmeticFunction

namespace TwinPrime.Analytic

def centeredQuadraticProductCoefficients {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) : ArithmeticFunction ℂ :=
  quadraticProductCoefficients χ₁ χ₂ -
    regularizedQuadraticLFunctionProduct χ₁ χ₂ 1 • (zeta : ArithmeticFunction ℂ)

theorem centeredQuadraticProductCoefficients_apply {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) (n : ℕ) (hn : n ≠ 0) :
    centeredQuadraticProductCoefficients χ₁ χ₂ n =
      quadraticProductCoefficients χ₁ χ₂ n - regularizedQuadraticLFunctionProduct χ₁ χ₂ 1 := by
  change quadraticProductCoefficients χ₁ χ₂ n -
    regularizedQuadraticLFunctionProduct χ₁ χ₂ 1 * (zeta : ArithmeticFunction ℂ) n = _
  simp [zeta_apply_ne hn]

theorem sum_Ioc_centeredQuadraticProductCoefficients {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, centeredQuadraticProductCoefficients χ₁ χ₂ n) =
      complexArithmeticSummatory (quadraticProductCoefficients χ₁ χ₂) (N : ℝ) -
        (N : ℂ) * regularizedQuadraticLFunctionProduct χ₁ χ₂ 1 := by
  have hsum : (∑ n ∈ Ioc 0 N, centeredQuadraticProductCoefficients χ₁ χ₂ n) =
      ∑ n ∈ Ioc 0 N, (quadraticProductCoefficients χ₁ χ₂ n -
        regularizedQuadraticLFunctionProduct χ₁ χ₂ 1) := by
    apply sum_congr rfl
    intro n hn
    exact centeredQuadraticProductCoefficients_apply χ₁ χ₂ n (ne_of_gt (mem_Ioc.mp hn).1)
  rw [hsum, sum_sub_distrib, complexArithmeticSummatory_nat]
  simp only [sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]

/-- The actual centered coefficients satisfy the prefix-power hypothesis
needed for ordered Dirichlet continuation; the zero prefix is included.-/
theorem norm_centeredQuadraticProductCoefficients_prefix_le {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hχ₁₂ : χ₁ * χ₂ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Ioc 0 N, centeredQuadraticProductCoefficients χ₁ χ₂ n‖ ≤
      (441 * (1 + 3250 * (q : ℝ) ^ 2)) * (N : ℝ) ^ (9 / 10 : ℝ) := by
  by_cases hN : N = 0
  · subst N
    simp [Real.zero_rpow (by norm_num : (9 / 10 : ℝ) ≠ 0)]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog : 1 + Real.log (N : ℝ) ≤ 21 * (N : ℝ) ^ (1 / 20 : ℝ) := by
    simpa only [one_div_one_div, show (1 + 20 : ℝ) = 21 by norm_num] using
      one_add_log_le_one_add_inv_mul_rpow (N : ℝ) (1 / 20) hN1 (by norm_num)
  have hpower : (N : ℝ) ^ (4 / 5 : ℝ) * ((N : ℝ) ^ (1 / 20 : ℝ)) ^ 2 =
      (N : ℝ) ^ (9 / 10 : ℝ) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg N), ← Real.rpow_add hN0]
    norm_num
  rw [sum_Ioc_centeredQuadraticProductCoefficients]
  apply (norm_quadraticProductCoefficients_summatory_sub_residue_le
    χ₁ χ₂ hχ₁ hχ₂ hχ₁₂ (N : ℝ) hN1).trans
  calc
    _ ≤ (1 + 3250 * (q : ℝ) ^ 2) * (N : ℝ) ^ (4 / 5 : ℝ) *
        (21 * (N : ℝ) ^ (1 / 20 : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith [Real.log_natCast_nonneg N]) hlog 2) (by positivity)
    _ = (441 * (1 + 3250 * (q : ℝ) ^ 2)) *
        ((N : ℝ) ^ (4 / 5 : ℝ) * ((N : ℝ) ^ (1 / 20 : ℝ)) ^ 2) := by ring
    _ = _ := by rw [hpower]

/-- The centered Dirichlet partial sum retains both original finite sums.-/
theorem powerDirichletPartialSum_centeredQuadraticProductCoefficients
    {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q) (s : ℂ) (N : ℕ) :
    powerDirichletPartialSum (centeredQuadraticProductCoefficients χ₁ χ₂) s N =
      quadraticProductDirichletPartialSum χ₁ χ₂ s N -
        regularizedQuadraticLFunctionProduct χ₁ χ₂ 1 *
          (∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-s)) := by
  unfold powerDirichletPartialSum quadraticProductDirichletPartialSum
  rw [mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro n hn
  rw [centeredQuadraticProductCoefficients_apply χ₁ χ₂ n (ne_of_gt (mem_Ioc.mp hn).1)]
  ring

end TwinPrime.Analytic
