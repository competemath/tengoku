import Tengoku.Piirrationalitymeasure.Formalization.ConstructionIntegral
import Tengoku.Piirrationalitymeasure.Formalization.PositivePowerAsymptotic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The actual positive generating function on the right side of (6.66). -/

namespace PiIrrationality

def constructionDegree (a b c : ℕ) : ℕ := 2 * a + 4 * b - 2 * c

noncomputable def constructionSeries (a b c : ℕ) : PowerSeries ℚ :=
  PositivePower.series (2 * a) b (constructionDegree a b c)

noncomputable def constructionSeriesValue (a b c : ℕ) (x : ℝ) : ℝ :=
  PositivePower.realValue (2 * a) b (constructionDegree a b c) x

noncomputable def constructionCoefficientScale (a b c : ℕ) : ℚ :=
  5 ^ (2 * (a + b - c)) * 2 ^ (4 * b - 2 * c)

noncomputable def constructionCoefficientExpression (a b c n : ℕ) : ℚ :=
  constructionCoefficientScale a b c ^ n / 4 *
    PowerSeries.coeff (c * n) (constructionSeries a b c ^ n)

theorem construction_admissible_inequalities {a b c : ℕ} (hc : 0 < c)
    (hp : Admissible (constructionParameter a b c)) :
    c < a + b ∧ c < 2 * b ∧ 7 * b < 5 * c ∧ 3 * c < 2 * a + 4 * b := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  dsimp [Admissible, constructionParameter] at hp
  have ha : (c : ℝ) < a + b := by
    have h : (1 : ℝ) < ((a : ℝ) + b) / c := by simpa only [add_div] using hp.1
    simpa using (lt_div_iff₀ hc').mp h
  have hb : (c : ℝ) < 2 * b := by
    have h : (1 : ℝ) < 2 * (b : ℝ) / c := by
      simpa only [mul_div_assoc] using hp.2.1
    simpa using (lt_div_iff₀ hc').mp h
  have h7 : (7 : ℝ) * b < 5 * c := by
    have h : 7 * (b : ℝ) / c < 5 := by
      simpa only [mul_div_assoc] using hp.2.2.1
    exact (div_lt_iff₀ hc').mp h
  have h3 : (3 : ℝ) * c < 2 * a + 4 * b := by
    have h : (3 : ℝ) < (2 * (a : ℝ) + 4 * b) / c := by
      rw [add_div, mul_div_assoc, mul_div_assoc]
      linarith [hp.2.2.2]
    exact (lt_div_iff₀ hc').mp h
  exact_mod_cast (show (c : ℝ) < a + b ∧ (c : ℝ) < 2 * b ∧
    (7 : ℝ) * b < 5 * c ∧ (3 : ℝ) * c < 2 * a + 4 * b from ⟨ha, hb, h7, h3⟩)

theorem constructionDegree_cast {a b c : ℕ} (h : 2 * c ≤ 2 * a + 4 * b) :
    (constructionDegree a b c : ℝ) = 2 * a + 4 * b - 2 * c := by
  simp only [constructionDegree, Nat.cast_sub h, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

theorem constructionDegree_pos {a b c : ℕ} (hc : 0 < c)
    (hp : Admissible (constructionParameter a b c)) : 0 < constructionDegree a b c := by
  have h := (construction_admissible_inequalities hc hp).2.2.2
  unfold constructionDegree
  omega

theorem constructionSeries_candidate : constructionSeries 1857 3714 5570 = Sseries := rfl

theorem constructionSeries_coeff_pos {a b c : ℕ} (hc : 0 < c)
    (hp : Admissible (constructionParameter a b c)) (n : ℕ) (hn : 0 < n) (k : ℕ) :
    0 < PowerSeries.coeff k (constructionSeries a b c ^ n) :=
  PositivePower.series_pow_coeff_pos (2 * a) b (constructionDegree_pos hc hp) hn k

theorem constructionCoefficientScale_pos (a b c : ℕ) : 0 < constructionCoefficientScale a b c := by
  unfold constructionCoefficientScale
  positivity

theorem constructionCoefficientExpression_pos {a b c : ℕ} (hc : 0 < c)
    (hp : Admissible (constructionParameter a b c)) (n : ℕ) :
    0 < constructionCoefficientExpression a b c n :=
  mul_pos (div_pos (pow_pos (constructionCoefficientScale_pos a b c) n) (by norm_num))
    (PositivePower.series_diagonal_coeff_pos (2 * a) b (constructionDegree_pos hc hp) c n)

theorem constructionCoefficientScale_log {a b c : ℕ} (hc : 0 < c)
    (hp : Admissible (constructionParameter a b c)) :
    Real.log (constructionCoefficientScale a b c : ℝ) =
      ((a : ℝ) + b - c) * Real.log 25 + (4 * (b : ℝ) - 2 * c) * Real.log 2 := by
  have h := construction_admissible_inequalities hc hp
  have hbc : 2 * c ≤ 4 * b := by omega
  have h25 : Real.log 25 = 2 * Real.log 5 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.log_pow]
    norm_num
  simp only [constructionCoefficientScale, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat,
    Real.log_mul (by positivity : (5 : ℝ) ^ (2 * (a + b - c)) ≠ 0)
      (by positivity : (2 : ℝ) ^ (4 * b - 2 * c) ≠ 0), Real.log_pow,
    Nat.cast_sub h.1.le, Nat.cast_sub hbc, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, h25]
  ring

end PiIrrationality
