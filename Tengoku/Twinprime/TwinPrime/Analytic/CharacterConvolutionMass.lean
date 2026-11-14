import Tengoku.Seed.NumberTheory.ArithmeticFunction.Misc
import Tengoku.Seed.NumberTheory.LSeries.Nonvanishing
import Tengoku.Seed.NumberTheory.Harmonic.Bounds
import Tengoku.Seed.Algebra.Order.Floor.Semiring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Absolute mass of bounded-coefficient Dirichlet convolutions

The finite divisor identity and the harmonic bound give logarithmic and
logarithmic-square masses for double and triple convolutions. No character
cancellation, nonprincipal hypothesis, or infinite-series assertion is used.
-/

noncomputable section

open Finset ArithmeticFunction

namespace TwinPrime.Analytic

/-- Absolute convolution mass is bounded by the corresponding nested sum.
@isnad1 id=le.0h3v.s7.407dda1abeec from=translated src=- shape=10ab4ffe vocab=893dec06
-/
theorem sum_norm_convolution_le_sum_sum (f g : ArithmeticFunction ℂ) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, ‖(f * g) n‖) ≤
      ∑ k ∈ Ioc 0 N, ‖f k‖ * ∑ d ∈ Ioc 0 (N / k), ‖g d‖ := by
  let nf : ArithmeticFunction ℝ := ⟨fun n => ‖f n‖, by simp⟩
  let ng : ArithmeticFunction ℝ := ⟨fun n => ‖g n‖, by simp⟩
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, (nf * ng) n := by
      apply sum_le_sum
      intro n _
      rw [mul_apply, mul_apply]
      simpa only [nf, ng, ArithmeticFunction.coe_mk, norm_mul] using
        (norm_sum_le n.divisorsAntidiagonal (fun d => f d.1 * g d.2))
    _ = _ := sum_Ioc_mul_eq_sum_sum nf ng N

/--
@isnad1 id=le.1h2v.s6.5005c4f2d45c from=translated src=- shape=d6fabf10 vocab=e82d5ef2
-/
theorem sum_norm_Ioc_le_nat (f : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, ‖f n‖) ≤ N := by
  calc
    _ ≤ ∑ _n ∈ Ioc 0 N, (1 : ℝ) := sum_le_sum (fun n _ => hf n)
    _ = _ := by simp

/-- A linear bound for one factor's mass costs one harmonic sum.
@isnad1 id=le.3h4v.s7.0595d81d2a82 from=translated src=- shape=370ff1c7 vocab=3e625879
-/
theorem sum_norm_convolution_le_of_linear_mass (f g : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ D ≤ N, (∑ n ∈ Ioc 0 D, ‖g n‖) ≤ (D : ℝ) * C) :
    (∑ n ∈ Ioc 0 N, ‖(f * g) n‖) ≤
      (N : ℝ) * C * (1 + Real.log N) := by
  have hsum := sum_norm_convolution_le_sum_sum f g N
  apply hsum.trans
  calc
    _ ≤ ∑ k ∈ Ioc 0 N, ((N / k : ℕ) : ℝ) * C := by
      apply sum_le_sum
      intro k _
      simpa only [one_mul] using
        (mul_le_mul (hf k) (hg (N / k) (Nat.div_le_self N k))
          (sum_nonneg (fun _ _ => norm_nonneg _)) (by norm_num : (0 : ℝ) ≤ 1))
    _ ≤ ∑ k ∈ Ioc 0 N, ((N : ℝ) / k) * C := by
      apply sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_right Nat.cast_div_le hC
    _ = (N : ℝ) * C * (harmonic N : ℝ) := by
      have hI : Ioc 0 N = Icc 1 N := by ext n; simp; omega
      rw [hI]
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      rw [mul_sum]
      apply sum_congr rfl
      intro k _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (by positivity)

/--
@isnad1 id=le.2h3v.s7.6e9df1b3ab4b from=translated src=- shape=ff531948 vocab=3e625879
-/
theorem sum_norm_convolution_le_mul_one_add_log_nat (f g : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, ‖(f * g) n‖) ≤ (N : ℝ) * (1 + Real.log N) := by
  simpa only [mul_one] using sum_norm_convolution_le_of_linear_mass f g hf N 1
    (by norm_num) (fun D _ => by simpa only [mul_one] using sum_norm_Ioc_le_nat g hg D)

/--
@isnad1 id=le.3h4v.s7.11bdf5f7e686 from=translated src=- shape=abd94c9a vocab=ed38a1a5
-/
theorem sum_norm_triple_convolution_le_mul_one_add_log_sq_nat
    (f g h : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1) (hh : ∀ n, ‖h n‖ ≤ 1)
    (N : ℕ) :
    (∑ n ∈ Ioc 0 N, ‖(f * g * h) n‖) ≤ (N : ℝ) * (1 + Real.log N) ^ 2 := by
  rw [mul_assoc]
  have hmass (D : ℕ) (hD : D ≤ N) :
      (∑ n ∈ Ioc 0 D, ‖(g * h) n‖) ≤ (D : ℝ) * (1 + Real.log N) := by
    by_cases hD0 : D = 0
    · simp [hD0]
    have hDpos : (0 : ℝ) < D := by exact_mod_cast Nat.pos_of_ne_zero hD0
    apply (sum_norm_convolution_le_mul_one_add_log_nat g h hg hh D).trans
    exact mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (Real.log_le_log hDpos (by exact_mod_cast hD : (D : ℝ) ≤ N)))
      (Nat.cast_nonneg D)
  have hbound := sum_norm_convolution_le_of_linear_mass f (g * h) hf N
    (1 + Real.log N) (by linarith [Real.log_natCast_nonneg N]) hmass
  convert hbound using 1
  ring

/--
@isnad1 id=le.2h2v.s6.e00d802682c9 from=translated src=- shape=8fc062e5 vocab=63e2f9a1
-/
theorem sum_norm_Ioc_floor_le (f : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (x : ℝ) (hx : 0 ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, ‖f n‖) ≤ x :=
  (sum_norm_Ioc_le_nat f hf ⌊x⌋₊).trans (Nat.floor_le hx)

/--
@isnad1 id=le.2h2v.s6.15deb39232cb from=translated src=- shape=a40b933b vocab=63e2f9a1
-/
theorem norm_sum_Ioc_floor_le (f : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (x : ℝ) (hx : 0 ≤ x) :
    ‖∑ n ∈ Ioc 0 ⌊x⌋₊, f n‖ ≤ x :=
  (norm_sum_le _ _).trans (sum_norm_Ioc_floor_le f hf x hx)

/-- The double convolution has absolute mass at most `x(1+log x)`.
@isnad1 id=le.3h3v.s7.aae5dae29536 from=translated src=- shape=5c0351aa vocab=b24ecf3f
-/
theorem sum_norm_convolution_le_mul_one_add_log (f g : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1) (x : ℝ) (hx : 1 ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, ‖(f * g) n‖) ≤ x * (1 + Real.log x) := by
  have hx0 : 0 ≤ x := by linarith
  have hN0 : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast Nat.floor_pos.mpr hx
  have hN := Nat.floor_le hx0
  have hlog := Real.log_le_log hN0 hN
  apply (sum_norm_convolution_le_mul_one_add_log_nat f g hf hg ⌊x⌋₊).trans
  exact mul_le_mul hN (add_le_add le_rfl hlog)
    (by linarith [Real.log_natCast_nonneg ⌊x⌋₊]) hx0

/-- The triple convolution has absolute mass at most `x(1+log x)²`.
@isnad1 id=le.4h4v.s7.d2b4842833eb from=translated src=- shape=fc00116a vocab=927a84de
-/
theorem sum_norm_triple_convolution_le_mul_one_add_log_sq
    (f g h : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1) (hh : ∀ n, ‖h n‖ ≤ 1)
    (x : ℝ) (hx : 1 ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, ‖(f * g * h) n‖) ≤ x * (1 + Real.log x) ^ 2 := by
  have hx0 : 0 ≤ x := by linarith
  have hN0 : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast Nat.floor_pos.mpr hx
  have hN := Nat.floor_le hx0
  have hlog := Real.log_le_log hN0 hN
  apply (sum_norm_triple_convolution_le_mul_one_add_log_sq_nat f g h hf hg hh ⌊x⌋₊).trans
  exact mul_le_mul hN
    (pow_le_pow_left₀ (by linarith [Real.log_natCast_nonneg ⌊x⌋₊])
      (add_le_add le_rfl hlog) 2) (sq_nonneg _) hx0

/--
@isnad1 id=le.0h3v.s6.16edfcdec858 from=translated src=- shape=b6f02992 vocab=5f8b6a5d
-/
theorem norm_characterArithmetic_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖toArithmeticFunction (χ ·) n‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [← χ.apply_eq_toArithmeticFunction_apply hn]
    exact χ.norm_le_one _

/--
@isnad1 id=le.1h3v.s6.6a9a58fe7597 from=translated src=- shape=6fea582e vocab=fdd31e17
-/
theorem sum_norm_characterArithmetic_le {q : ℕ} (χ : DirichletCharacter ℂ q)
    (x : ℝ) (hx : 0 ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, ‖toArithmeticFunction (χ ·) n‖) ≤ x :=
  sum_norm_Ioc_floor_le _ (norm_characterArithmetic_le_one χ) x hx

/--
@isnad1 id=le.1h3v.s6.b805a9288765 from=translated src=- shape=82ba731c vocab=fdd31e17
-/
theorem norm_sum_characterArithmetic_le {q : ℕ} (χ : DirichletCharacter ℂ q)
    (x : ℝ) (hx : 0 ≤ x) :
    ‖∑ n ∈ Ioc 0 ⌊x⌋₊, toArithmeticFunction (χ ·) n‖ ≤ x :=
  norm_sum_Ioc_floor_le _ (norm_characterArithmetic_le_one χ) x hx

/--
@isnad1 id=le.1h5v.s7.d04e2cf74a71 from=translated src=- shape=f5c1f338 vocab=cc915db8
-/
theorem sum_norm_two_character_convolution_le {q₁ q₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (x : ℝ) (hx : 1 ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊,
      ‖(toArithmeticFunction (χ₁ ·) * toArithmeticFunction (χ₂ ·)) n‖) ≤
        x * (1 + Real.log x) :=
  sum_norm_convolution_le_mul_one_add_log _ _
    (norm_characterArithmetic_le_one χ₁) (norm_characterArithmetic_le_one χ₂) x hx

/--
@isnad1 id=le.1h7v.s8.0aab145fb1f3 from=translated src=- shape=6cc4cf23 vocab=422d80b3
-/
theorem sum_norm_three_character_convolution_le {q₁ q₂ q₃ : ℕ}
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (χ₃ : DirichletCharacter ℂ q₃) (x : ℝ) (hx : 1 ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊,
      ‖(toArithmeticFunction (χ₁ ·) * toArithmeticFunction (χ₂ ·) *
        toArithmeticFunction (χ₃ ·)) n‖) ≤ x * (1 + Real.log x) ^ 2 :=
  sum_norm_triple_convolution_le_mul_one_add_log_sq _ _ _
    (norm_characterArithmetic_le_one χ₁) (norm_characterArithmetic_le_one χ₂)
    (norm_characterArithmetic_le_one χ₃) x hx

end TwinPrime.Analytic
