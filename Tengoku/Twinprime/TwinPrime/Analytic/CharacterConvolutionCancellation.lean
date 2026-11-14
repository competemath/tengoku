import Tengoku.Twinprime.TwinPrime.Analytic.ConvolutionHyperbolaBound
import Tengoku.Twinprime.TwinPrime.Analytic.CharacterPeriodSum
import Tengoku.Twinprime.TwinPrime.Analytic.CharacterConvolutionMass
import Tengoku.Twinprime.TwinPrime.Analytic.ReciprocalPowerSums

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cancellation for two and three nonprincipal character convolutions

Complete-period cancellation and exact real-endpoint hyperbola identities
give the square-root pair bound and a two-thirds-power triple bound.
All factors are actual character arithmetic functions; no primitivity or
prime-distribution estimate is used.
-/

noncomputable section

open Finset ArithmeticFunction

namespace TwinPrime.Analytic

/--
@isnad1 id=eq.0h3v.s7.a94a76e3dde0 from=translated src=- shape=4dc63b59 vocab=22f2f2a5
-/
theorem sum_characterArithmetic_Ioc_eq {q : ℕ}
    (χ : DirichletCharacter ℂ q) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, toArithmeticFunction (χ ·) n) =
      ∑ n ∈ Ioc 0 N, χ (n : ZMod q) := by
  apply sum_congr rfl
  intro n hn
  exact (χ.apply_eq_toArithmeticFunction_apply (ne_of_gt (mem_Ioc.mp hn).1)).symm

/--
@isnad1 id=le.1h3v.s7.a4905a3dcb86 from=translated src=- shape=4c76525c vocab=f82bceb2
-/
theorem norm_characterArithmetic_sum_le_modulus {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Ioc 0 N, toArithmeticFunction (χ ·) n‖ ≤ (q : ℝ) := by
  rw [sum_characterArithmetic_Ioc_eq]
  exact norm_character_sum_Ioc_le_modulus χ hχ N

/--
@isnad1 id=le.1h3v.s7.f90d853fb6ef from=translated src=- shape=ad4745b2 vocab=9eb21ec9
-/
theorem norm_complexArithmeticSummatory_character_le_modulus {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (x : ℝ) :
    ‖complexArithmeticSummatory (toArithmeticFunction (χ ·)) x‖ ≤ (q : ℝ) :=
  norm_characterArithmetic_sum_le_modulus χ hχ ⌊x⌋₊

/-- Each nonprincipal factor supplies its actual complete-period bound.
@isnad1 id=le.3h4v.s8.a82b9aff95cb from=translated src=- shape=616428e1 vocab=f986f32a
-/
theorem norm_two_character_convolution_summatory_le {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1)
    (x : ℝ) (hx : 1 ≤ x) :
    ‖complexArithmeticSummatory
      (toArithmeticFunction (χ₁ ·) * toArithmeticFunction (χ₂ ·)) x‖ ≤
        3 * (q : ℝ) * Real.sqrt x :=
  norm_convolution_summatory_le_three_mul_sqrt _ _
    (norm_characterArithmetic_le_one χ₁) (norm_characterArithmetic_le_one χ₂)
    q (Nat.cast_nonneg q) (norm_characterArithmetic_sum_le_modulus χ₁ hχ₁)
    (norm_characterArithmetic_sum_le_modulus χ₂ hχ₂) x hx

/-- The real hyperbola cutoffs `x^(2/3)` and `x^(1/3)` give a uniform
triple-convolution bound, including imprimitive nonprincipal characters.
@isnad1 id=le.4h5v.s9.db1d3384b0bf from=translated src=- shape=0b29c6f5 vocab=f9a61c0a
-/
theorem norm_three_character_convolution_summatory_le {q : ℕ} [NeZero q]
    (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hχ₃ : χ₃ ≠ 1)
    (x : ℝ) (hx : 1 ≤ x) :
    ‖complexArithmeticSummatory
      (toArithmeticFunction (χ₁ ·) * toArithmeticFunction (χ₂ ·) *
        toArithmeticFunction (χ₃ ·)) x‖ ≤
      10 * (q : ℝ) ^ 2 * x ^ (2 / 3 : ℝ) * (1 + Real.log x) := by
  let f : ArithmeticFunction ℂ :=
    toArithmeticFunction (χ₁ ·) * toArithmeticFunction (χ₂ ·)
  let g : ArithmeticFunction ℂ := toArithmeticFunction (χ₃ ·)
  let y : ℝ := x ^ (2 / 3 : ℝ)
  let z : ℝ := x ^ (1 / 3 : ℝ)
  have hx0 : 0 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hy : 1 ≤ y := Real.one_le_rpow hx (by norm_num)
  have hz : 1 ≤ z := Real.one_le_rpow hx (by norm_num)
  have hy0 : 0 ≤ y := by linarith
  have hz0 : 0 ≤ z := by linarith
  have hyx : y ≤ x := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (2 / 3 : ℝ) ≤ 1))
  have hzx : z ≤ x := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (1 / 3 : ℝ) ≤ 1))
  have hyz : y * z = x := by
    dsimp [y, z]
    rw [← Real.rpow_add hxpos]
    norm_num
  have hsqrt : Real.sqrt x * Real.sqrt z = y := by
    dsimp [y, z]
    simp only [Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul hx0, ← Real.rpow_add hxpos]
    norm_num
  have hsqrty : Real.sqrt y ≤ y :=
    (Real.sqrt_le_iff).mpr ⟨hy0, by nlinarith⟩
  have hlog : Real.log y ≤ Real.log x := Real.log_le_log (by linarith) hyx
  have hL : 1 ≤ 1 + Real.log x := by linarith [Real.log_nonneg hx]
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hq2 : (q : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
  have hA : ‖∑ k ∈ Ioc 0 ⌊y⌋₊, f k * complexArithmeticSummatory g (x / k)‖ ≤
      (q : ℝ) * y * (1 + Real.log x) := by
    calc
      _ ≤ ∑ k ∈ Ioc 0 ⌊y⌋₊, ‖f k * complexArithmeticSummatory g (x / k)‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Ioc 0 ⌊y⌋₊, ‖f k‖ * (q : ℝ) := by
        apply sum_le_sum
        intro k _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          (norm_complexArithmeticSummatory_character_le_modulus χ₃ hχ₃ _) (norm_nonneg _)
      _ = (∑ k ∈ Ioc 0 ⌊y⌋₊, ‖f k‖) * (q : ℝ) := (sum_mul _ _ _).symm
      _ ≤ (y * (1 + Real.log y)) * (q : ℝ) :=
        mul_le_mul_of_nonneg_right (sum_norm_two_character_convolution_le χ₁ χ₂ y hy) hq0
      _ ≤ (y * (1 + Real.log x)) * (q : ℝ) := by
        gcongr
      _ = _ := by ring
  have hB : ‖∑ d ∈ Ioc 0 ⌊z⌋₊, g d * complexArithmeticSummatory f (x / d)‖ ≤
      6 * (q : ℝ) * y := by
    calc
      _ ≤ ∑ d ∈ Ioc 0 ⌊z⌋₊, ‖g d * complexArithmeticSummatory f (x / d)‖ := norm_sum_le _ _
      _ ≤ ∑ d ∈ Ioc 0 ⌊z⌋₊, 3 * (q : ℝ) * Real.sqrt x * (1 / Real.sqrt (d : ℝ)) := by
        apply sum_le_sum
        intro d hd
        have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Ioc.mp hd).1
        have hdx : (d : ℝ) ≤ x :=
          (Nat.cast_le.mpr (mem_Ioc.mp hd).2).trans ((Nat.floor_le hz0).trans hzx)
        have hquot : 1 ≤ x / d := (le_div_iff₀ hd0).mpr (by simpa using hdx)
        rw [norm_mul]
        calc
          _ ≤ ‖complexArithmeticSummatory f (x / d)‖ :=
            mul_le_of_le_one_left (norm_nonneg _) (norm_characterArithmetic_le_one χ₃ d)
          _ ≤ 3 * (q : ℝ) * Real.sqrt (x / d) :=
            norm_two_character_convolution_summatory_le χ₁ χ₂ hχ₁ hχ₂ _ hquot
          _ = _ := by rw [Real.sqrt_div hx0]; ring
      _ = (3 * (q : ℝ) * Real.sqrt x) *
          (∑ d ∈ Ioc 0 ⌊z⌋₊, 1 / Real.sqrt (d : ℝ)) := (mul_sum _ _ _).symm
      _ ≤ (3 * (q : ℝ) * Real.sqrt x) * (2 * Real.sqrt z) :=
        mul_le_mul_of_nonneg_left (sum_Ioc_natFloor_one_div_sqrt_le z hz0) (by positivity)
      _ = 6 * (q : ℝ) * (Real.sqrt x * Real.sqrt z) := by ring
      _ = _ := by rw [hsqrt]
  have hO : ‖complexArithmeticSummatory f y * complexArithmeticSummatory g z‖ ≤
      3 * (q : ℝ) ^ 2 * y := by
    rw [norm_mul]
    calc
      _ ≤ (3 * (q : ℝ) * Real.sqrt y) * (q : ℝ) :=
        mul_le_mul (norm_two_character_convolution_summatory_le χ₁ χ₂ hχ₁ hχ₂ y hy)
          (norm_complexArithmeticSummatory_character_le_modulus χ₃ hχ₃ z)
          (norm_nonneg _) (by positivity)
      _ ≤ (3 * (q : ℝ) * y) * (q : ℝ) := by gcongr
      _ = _ := by ring
  have hA' : (q : ℝ) * y * (1 + Real.log x) ≤
      (q : ℝ) ^ 2 * y * (1 + Real.log x) := by gcongr
  have hB' : 6 * (q : ℝ) * y ≤ 6 * (q : ℝ) ^ 2 * y * (1 + Real.log x) := by
    calc
      _ ≤ 6 * (q : ℝ) ^ 2 * y := by gcongr
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hL
  have hO' : 3 * (q : ℝ) ^ 2 * y ≤ 3 * (q : ℝ) ^ 2 * y * (1 + Real.log x) :=
    le_mul_of_one_le_right (by positivity) hL
  change ‖complexArithmeticSummatory (f * g) x‖ ≤ _
  rw [complexArithmeticSummatory_convolution_hyperbola f g x y z hx hy hz hyz]
  have htriangle := (norm_sub_le
    ((∑ k ∈ Ioc 0 ⌊y⌋₊, f k * complexArithmeticSummatory g (x / k)) +
      ∑ d ∈ Ioc 0 ⌊z⌋₊, g d * complexArithmeticSummatory f (x / d))
    (complexArithmeticSummatory f y * complexArithmeticSummatory g z)).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  change _ ≤ 10 * (q : ℝ) ^ 2 * y * (1 + Real.log x)
  linarith

end TwinPrime.Analytic
