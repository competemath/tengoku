import Tengoku.Twinprime.TwinPrime.Analytic.CharacterConvolutionContinuation
import Tengoku.Seed.NumberTheory.Harmonic.Bounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Nonprincipal L-function bounds from complete periods

The elementary modulus bound for character prefixes gives ordered
continuation throughout the positive half-plane, without primitivity.
At one, truncation at the modulus costs at most four, while its finite
head is bounded by the harmonic sum.
-/

noncomputable section

open Finset Filter
open scoped Topology

namespace TwinPrime.Analytic

private theorem characterArithmetic_prefix_le_power_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Ioc 0 N, toArithmeticFunction (χ ·) n‖ ≤ (q : ℝ) * (N : ℝ) ^ (0 : ℝ) := by
  simpa only [Real.rpow_zero, mul_one] using norm_characterArithmetic_sum_le_modulus χ hχ N

/-- The actual L-function is the ordered character-series limit throughout
the positive half-plane, including for imprimitive nonprincipal characters.-/
theorem powerDirichletLimit_character_eqOn {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Set.EqOn (powerDirichletLimit (toArithmeticFunction (χ ·)))
      (DirichletCharacter.LFunction χ) {s : ℂ | 0 < s.re} := by
  apply powerDirichletLimit_eqOn_of_LSeries_right 0 (by norm_num) _ q (Nat.cast_nonneg q)
    (characterArithmetic_prefix_le_power_zero χ hχ) _
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
  · intro s hs
    exact LSeriesSummable_characterArithmeticFunction χ ((le_max_right (0 : ℝ) 1).trans_lt hs)
  · intro s hs
    exact LSeries_characterArithmeticFunction χ ((le_max_right (0 : ℝ) 1).trans_lt hs)

theorem tendstoLocallyUniformlyOn_character_powerDirichletPartialSum_LFunction
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    TendstoLocallyUniformlyOn
      (fun N s => powerDirichletPartialSum (toArithmeticFunction (χ ·)) s N)
      (DirichletCharacter.LFunction χ) atTop {s : ℂ | 0 < s.re} :=
  (tendstoLocallyUniformlyOn_powerDirichletPartialSum_limit 0 (by norm_num) _ q
    (Nat.cast_nonneg q) (characterArithmetic_prefix_le_power_zero χ hχ)).congr_right
      (powerDirichletLimit_character_eqOn χ hχ)

theorem tendsto_character_powerDirichletPartialSum_LFunction
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (s : ℂ) (hs : 0 < s.re) :
    Tendsto (powerDirichletPartialSum (toArithmeticFunction (χ ·)) s) atTop
      (𝓝 (DirichletCharacter.LFunction χ s)) := by
  rw [← powerDirichletLimit_character_eqOn χ hχ hs]
  exact tendsto_powerDirichletPartialSum_limit 0 (by norm_num) _ q
    (Nat.cast_nonneg q) (characterArithmetic_prefix_le_power_zero χ hχ) s hs

/-- A period bound gives a quantitative truncation estimate on `Re(s)>0`.
This is an ordered-series estimate, not an absolute-summability assertion.-/
theorem norm_LFunction_sub_powerDirichletPartialSum_le_of_nonprincipal
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (M : ℕ) (hM : 1 ≤ M) (s : ℂ) (hs : 0 < s.re) :
    ‖DirichletCharacter.LFunction χ s -
      powerDirichletPartialSum (toArithmeticFunction (χ ·)) s M‖ ≤
      (2 * (q : ℝ)) * (M : ℝ) ^ (-s.re) * (1 + ‖s‖ / s.re) := by
  simpa only [zero_sub, sub_zero] using
    norm_sub_powerDirichletPartialSum_le_of_eqOn 0 (by norm_num) _ q (Nat.cast_nonneg q)
      (characterArithmetic_prefix_le_power_zero χ hχ) _
      (powerDirichletLimit_character_eqOn χ hχ) M hM s hs

/-- The finite reciprocal head needs no nonprincipal or positive-modulus hypothesis.-/
theorem norm_character_reciprocal_partialSum_le_one_add_log {q : ℕ}
    (χ : DirichletCharacter ℂ q) (M : ℕ) :
    ‖powerDirichletPartialSum (toArithmeticFunction (χ ·)) 1 M‖ ≤ 1 + Real.log M := by
  rw [powerDirichletPartialSum_one_eq_reciprocal]
  calc
    _ ≤ ∑ n ∈ Ioc 0 M, ‖toArithmeticFunction (χ ·) n / (n : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Ioc 0 M, 1 / (n : ℝ) := by
      apply sum_le_sum
      intro n _
      rw [norm_div, Complex.norm_natCast]
      exact div_le_div_of_nonneg_right (norm_characterArithmetic_le_one χ n) (Nat.cast_nonneg n)
    _ ≤ _ := by
      have hI : Ioc 0 M = Icc 1 M := by ext n; simp; omega
      rw [hI]
      simpa only [one_div, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
        using harmonic_le_one_add_log M

/-- A uniform logarithmic upper bound for every nonprincipal character,
including imprimitive characters at any positive modulus.-/
theorem norm_LFunction_one_le_five_add_log {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ‖DirichletCharacter.LFunction χ 1‖ ≤ 5 + Real.log q := by
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have htail := norm_LFunction_sub_powerDirichletPartialSum_le_of_nonprincipal
    χ hχ q hq 1 (by norm_num)
  have hfour : (2 * (q : ℝ)) * (q : ℝ) ^ (-(1 : ℂ).re) *
      (1 + ‖(1 : ℂ)‖ / (1 : ℂ).re) = 4 := by
    simp only [Complex.one_re, norm_one, div_one, Real.rpow_neg_one]
    field_simp
    ring
  rw [hfour] at htail
  have hhead := norm_character_reciprocal_partialSum_le_one_add_log χ q
  have htriangle := norm_add_le
    (DirichletCharacter.LFunction χ 1 - powerDirichletPartialSum (toArithmeticFunction (χ ·)) 1 q)
    (powerDirichletPartialSum (toArithmeticFunction (χ ·)) 1 q)
  rw [sub_add_cancel] at htriangle
  linarith

end TwinPrime.Analytic
