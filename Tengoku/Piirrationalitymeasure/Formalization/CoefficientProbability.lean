import Tengoku.Piirrationalitymeasure.Formalization.CoefficientConvergence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The tilted coefficient distributions and their convolution identity in (4.7). -/

namespace PiIrrationality

open PowerSeries

noncomputable def coefficientProbability (x : ℝ) (n k : ℕ) : ℝ :=
  (coeff k (Sseries ^ n) : ℚ) * x ^ k / SReal x ^ n

/--
@isnad1 id=le.2h3v.s5.f72713cb68fc from=translated src=- shape=5fb316b0 vocab=d7d1b562
-/
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

/--
@isnad1 id=lt.3h3v.s5.89f4d5edc87d from=translated src=- shape=fe15b075 vocab=8e52d1d5
-/
theorem coefficientProbability_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    {n : ℕ} (hn : 0 < n) (k : ℕ) : 0 < coefficientProbability x n k := by
  exact div_pos (mul_pos (by exact_mod_cast Sseries_pow_coeff_pos hn k) (pow_pos hx0 _))
    (pow_pos (SReal_pos hx0.le hx1) _)

/--
@isnad1 id=hassum.2h2v.s5.ef0361b1805d from=translated src=- shape=fcdbf59e vocab=b1c09f29
-/
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

/--
@isnad1 id=eq.2h3v.s5.6217086c2717 from=translated src=- shape=53dc966f vocab=431c201e
-/
theorem coefficientLaw_toReal {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n k : ℕ) :
    (coefficientLaw x hx0 hx1 n k).toReal = coefficientProbability x n k :=
  ENNReal.toReal_ofReal (coefficientProbability_nonneg hx0 hx1 n k)

/--
@isnad1 id=eq.3h2v.s5.eb133e2f090c from=translated src=- shape=0eb358e4 vocab=100fce52
-/
theorem coefficientLaw_full_support {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    {n : ℕ} (hn : 0 < n) : (coefficientLaw x hx0.le hx1 n).support = Set.univ := by
  ext k
  simp only [PMF.mem_support_iff, Set.mem_univ, iff_true]
  exact (ENNReal.ofReal_pos.mpr (coefficientProbability_pos hx0 hx1 hn k)).ne'

/--
@isnad1 id=eq.2h4v.s6.8b5da6454ea1 from=translated src=- shape=ff24a1c3 vocab=98a42ada
-/
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

/--
@isnad1 id=eq.2h3v.s7.e43f43d49531 from=translated src=- shape=1d0404d3 vocab=94c6215d
-/
theorem coefficientLaw_extraction {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (n k : ℕ) :
    (↑(coeff k (Sseries ^ n)) : ℝ) = SReal x ^ n / x ^ k *
      (coefficientLaw x hx0.le hx1 n k).toReal := by
  rw [coefficientLaw_toReal, coefficientProbability]
  field_simp [hx0.ne', SReal_ne_zero hx0.le hx1]

/--
@isnad1 id=hassum.2h3v.s6.80e9396a8fbf from=translated src=- shape=cd66bab3 vocab=4c083830
-/
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

/--
@isnad1 id=ex.2h2v.s6.91186a6b120e from=translated src=- shape=81c291cc vocab=84313829
-/
theorem coefficientProbability_exponential_moment {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (n : ℕ) : ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ →
      Summable (fun k => coefficientProbability x n k * Real.exp ((k : ℝ) * t)) := by
  refine ⟨-Real.log x, neg_pos.mpr (Real.log_neg hx0 hx1), fun t ht => ?_⟩
  apply (coefficientProbability_exponential_sum hx0.le n t ?_).summable
  calc
    x * Real.exp t = Real.exp (Real.log x + t) := by rw [Real.exp_add, Real.exp_log hx0]
    _ < 1 := Real.exp_lt_one_iff.mpr (by have h := lt_of_le_of_lt (le_abs_self t) ht; linarith)

end PiIrrationality
