import Tengoku.Piirrationalitymeasure.Formalization.CoefficientConvergence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The tilted coefficient distributions and their convolution identity in (4.7). -/

namespace PiIrrationality

open PowerSeries

noncomputable def coefficientProbability (x : ℝ) (n k : ℕ) : ℝ :=
  (coeff k (Sseries ^ n) : ℚ) * x ^ k / SReal x ^ n

theorem coefficientProbability_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n k : ℕ) :
    0 ≤ coefficientProbability x n k := by
  have hc : (0 : ℚ) ≤ coeff k (Sseries ^ n) := by
    by_cases hn : n = 0
    · subst n
      simp only [pow_zero, coeff_one]
      split <;> norm_num
    · exact (Sseries_pow_coeff_pos (Nat.pos_of_ne_zero hn) k).le
  exact div_nonneg (mul_nonneg (by exact_mod_cast hc) (pow_nonneg hx0 _))
    (pow_nonneg (SReal_pos hx0 hx1).le _)

theorem coefficientProbability_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    {n : ℕ} (hn : 0 < n) (k : ℕ) : 0 < coefficientProbability x n k := by
  exact div_pos (mul_pos (by exact_mod_cast Sseries_pow_coeff_pos hn k) (pow_pos hx0 _))
    (pow_pos (SReal_pos hx0.le hx1) _)

theorem coefficientProbability_hasSum {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    HasSum (coefficientProbability x n) 1 := by
  convert! (Sseries_pow_hasSum_real hx0 hx1 n).div_const (SReal x ^ n) using 1
  exact (div_self (pow_ne_zero _ (SReal_ne_zero hx0 hx1))).symm

noncomputable def coefficientLaw (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) : PMF ℕ :=
  ⟨fun k => ENNReal.ofReal (coefficientProbability x n k), by
    have h := coefficientProbability_hasSum hx0 hx1 n
    have ht := ENNReal.ofReal_tsum_of_nonneg
      (coefficientProbability_nonneg hx0 hx1 n) h.summable
    rw [h.tsum_eq, ENNReal.ofReal_one] at ht
    exact ht ▸ ENNReal.summable.hasSum⟩

theorem coefficientLaw_toReal {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n k : ℕ) :
    (coefficientLaw x hx0 hx1 n k).toReal = coefficientProbability x n k :=
  ENNReal.toReal_ofReal (coefficientProbability_nonneg hx0 hx1 n k)

theorem coefficientLaw_full_support {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    {n : ℕ} (hn : 0 < n) : (coefficientLaw x hx0.le hx1 n).support = Set.univ := by
  ext k
  simp only [PMF.mem_support_iff, Set.mem_univ, iff_true]
  exact (ENNReal.ofReal_pos.mpr (coefficientProbability_pos hx0 hx1 hn k)).ne'

theorem coefficientProbability_convolution {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (n m k : ℕ) :
    coefficientProbability x (n + m) k =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
        coefficientProbability x n p.1 * coefficientProbability x m p.2 := by
  unfold coefficientProbability
  rw [pow_add Sseries, coeff_mul, Rat.cast_sum, Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  have hk := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [Rat.cast_mul, ← hk, pow_add, pow_add]
  field_simp [SReal_ne_zero hx0 hx1]

theorem coefficientLaw_extraction {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (n k : ℕ) :
    (↑(coeff k (Sseries ^ n)) : ℝ) = SReal x ^ n / x ^ k *
      (coefficientLaw x hx0.le hx1 n k).toReal := by
  rw [coefficientLaw_toReal, coefficientProbability]
  field_simp [hx0.ne', SReal_ne_zero hx0.le hx1]

theorem coefficientProbability_exponential_sum {x : ℝ} (hx0 : 0 ≤ x)
    (n : ℕ) (t : ℝ) (ht : x * Real.exp t < 1) :
    HasSum (fun k => coefficientProbability x n k * Real.exp ((k : ℝ) * t))
      (SReal (x * Real.exp t) ^ n / SReal x ^ n) := by
  have h := (Sseries_pow_hasSum_real
    (mul_nonneg hx0 (Real.exp_pos t).le) ht n).div_const (SReal x ^ n)
  convert! h using 1
  ext k
  rw [Real.exp_nat_mul, mul_pow]
  dsimp [coefficientProbability]
  ring

theorem coefficientProbability_exponential_moment {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (n : ℕ) : ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ →
      Summable (fun k => coefficientProbability x n k * Real.exp ((k : ℝ) * t)) := by
  refine ⟨-Real.log x, neg_pos.mpr (Real.log_neg hx0 hx1), fun t ht => ?_⟩
  apply (coefficientProbability_exponential_sum hx0.le n t ?_).summable
  calc
    x * Real.exp t = Real.exp (Real.log x + t) := by rw [Real.exp_add, Real.exp_log hx0]
    _ < 1 := Real.exp_lt_one_iff.mpr (by have h := lt_of_le_of_lt (le_abs_self t) ht; linarith)

end PiIrrationality
