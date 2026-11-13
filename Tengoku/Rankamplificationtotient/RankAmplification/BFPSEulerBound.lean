import Tengoku.Rankamplificationtotient.RankAmplification.BFPSRankin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Bounding the BFPS Euler product by a smooth-predecessor prime sum The logarithm of the Euler product in `BFPSRankin` is bounded here by a constant multiple of `∑ p⁻ᶜ` over primes whose predecessor is smooth. -/

namespace RankAmplification

open scoped BigOperators

noncomputable section

/-- The prime Dirichlet sum appearing after the BFPS Euler-product reduction.-/
def smoothPredecessorPrimeRpowSum (X Y : ℕ) (c : ℝ) : ℝ :=
  ∑ p ∈ smoothPredecessorPrimeSet X Y, (p : ℝ) ^ (-c)

theorem smoothPredecessorPrimeRpowSum_nonneg (X Y : ℕ) (c : ℝ) :
    0 ≤ smoothPredecessorPrimeRpowSum X Y c := by
  exact Finset.sum_nonneg fun p hp ↦ Real.rpow_nonneg (Nat.cast_nonneg p) _

/-- Uniform loss from replacing every local Euler denominator by its value at the prime `2`.-/
def smoothPredecessorEulerLoss (c₀ : ℝ) : ℝ :=
  (1 - (2 : ℝ) ^ (-c₀))⁻¹

theorem smoothPredecessorEulerLoss_pos {c₀ : ℝ} (hc₀ : 0 < c₀) :
    0 < smoothPredecessorEulerLoss c₀ := by
  apply inv_pos.mpr
  exact sub_pos.mpr <| Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hc₀)

/-- A local Euler denominator at exponent `c ≥ c₀` is at least the denominator at `(2,c₀)`.-/
theorem one_sub_two_rpow_le_one_sub_prime_rpow {p : ℕ} (hp : p.Prime)
    {c₀ c : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c) :
    1 - (2 : ℝ) ^ (-c₀) ≤ 1 - (p : ℝ) ^ (-c) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hbase : (p : ℝ) ^ (-c) ≤ (2 : ℝ) ^ (-c) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
  have hexp : (2 : ℝ) ^ (-c) ≤ (2 : ℝ) ^ (-c₀) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  linarith

/-- The rational local factor is bounded by the worst denominator times `p⁻ᶜ`.-/
theorem rankinRatio_div_one_sub_le_loss_mul {p : ℕ} (hp : p.Prime)
    {c₀ c : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c) :
    (p : ℝ) ^ (-c) / (1 - (p : ℝ) ^ (-c)) ≤
      smoothPredecessorEulerLoss c₀ * (p : ℝ) ^ (-c) := by
  have hden0 : 0 < 1 - (2 : ℝ) ^ (-c₀) :=
    sub_pos.mpr <| Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hc₀)
  have hden := one_sub_two_rpow_le_one_sub_prime_rpow hp hc₀ hc
  have hinv : (1 - (p : ℝ) ^ (-c))⁻¹ ≤ (1 - (2 : ℝ) ^ (-c₀))⁻¹ := by
    exact inv_anti₀ hden0 hden
  have hq : 0 ≤ (p : ℝ) ^ (-c) := Real.rpow_nonneg (Nat.cast_nonneg p) _
  rw [div_eq_mul_inv, smoothPredecessorEulerLoss]
  nlinarith

/-- The complete Euler logarithm is controlled by the smooth-predecessor prime Dirichlet sum.-/
theorem log_smoothPredecessorEulerProduct_le_loss_mul_sum {X Y : ℕ}
    {c₀ c : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c) :
    Real.log (smoothPredecessorEulerProduct X Y c) ≤
      smoothPredecessorEulerLoss c₀ * smoothPredecessorPrimeRpowSum X Y c := by
  have hcpos : 0 < c := hc₀.trans_le hc
  calc
    Real.log (smoothPredecessorEulerProduct X Y c) ≤
        ∑ p ∈ smoothPredecessorPrimeSet X Y,
          (p : ℝ) ^ (-c) / (1 - (p : ℝ) ^ (-c)) :=
      log_smoothPredecessorEulerProduct_le hcpos
    _ ≤ ∑ p ∈ smoothPredecessorPrimeSet X Y,
        smoothPredecessorEulerLoss c₀ * (p : ℝ) ^ (-c) := by
      apply Finset.sum_le_sum
      intro p hp
      exact rankinRatio_div_one_sub_le_loss_mul
        (smoothPredecessorPrimeSet_prime hp) hc₀ hc
    _ = smoothPredecessorEulerLoss c₀ * smoothPredecessorPrimeRpowSum X Y c := by
      rw [smoothPredecessorPrimeRpowSum, Finset.mul_sum]

/-- Positivity of the finite BFPS Euler product.-/
theorem smoothPredecessorEulerProduct_pos {X Y : ℕ} {c : ℝ} (hc : 0 < c) :
    0 < smoothPredecessorEulerProduct X Y c := by
  rw [smoothPredecessorEulerProduct, rankinEulerMajorant]
  apply Finset.prod_pos
  intro p hp
  have hpPrime := smoothPredecessorPrimeSet_prime hp
  exact pow_pos
    (inv_pos.mpr <| sub_pos.mpr <|
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hpPrime.one_lt)
        (neg_lt_zero.mpr hc)) _

/-- Exponentiating the preceding logarithmic bound.-/
theorem smoothPredecessorEulerProduct_le_exp_loss_mul_sum {X Y : ℕ}
    {c₀ c : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c) :
    smoothPredecessorEulerProduct X Y c ≤
      Real.exp (smoothPredecessorEulerLoss c₀ * smoothPredecessorPrimeRpowSum X Y c) := by
  have hcpos : 0 < c := hc₀.trans_le hc
  rw [← Real.exp_log (smoothPredecessorEulerProduct_pos hcpos)]
  exact Real.exp_le_exp.mpr (log_smoothPredecessorEulerProduct_le_loss_mul_sum hc₀ hc)

/-- BFPS equation (2.2) with the Euler product replaced by its prime-sum exponential majorant.-/
theorem smoothTotientCount_le_rankinPrimeSum {X Y : ℕ} {c₀ c : ℝ}
    (hc₀ : 0 < c₀) (hc : c₀ ≤ c) :
    (smoothTotientCount X Y : ℝ) ≤
      (X : ℝ) ^ c *
        Real.exp (smoothPredecessorEulerLoss c₀ * smoothPredecessorPrimeRpowSum X Y c) := by
  exact (smoothTotientCount_le_rankinEuler (hc₀.trans_le hc)).trans <|
    mul_le_mul_of_nonneg_left
      (smoothPredecessorEulerProduct_le_exp_loss_mul_sum hc₀ hc)
      (Real.rpow_nonneg (Nat.cast_nonneg X) _)

/-- Rewriting the Rankin power exposes the saving `(1-c) log X`.-/
theorem rpow_eq_mul_exp_neg_one_sub {X : ℕ} (hX : 0 < X) (c : ℝ) :
    (X : ℝ) ^ c = (X : ℝ) * Real.exp (-(1 - c) * Real.log X) := by
  have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
  rw [Real.rpow_def_of_pos hXreal]
  have hexponent : Real.log (X : ℝ) * c =
      Real.log (X : ℝ) + (-(1 - c) * Real.log X) := by ring
  rw [hexponent, Real.exp_add, Real.exp_log hXreal]

/-- Final exponential form of the unconditional BFPS Rankin reduction.-/
theorem smoothTotientCount_le_exp_saving {X Y : ℕ} {c₀ c : ℝ}
    (hX : 0 < X) (hc₀ : 0 < c₀) (hc : c₀ ≤ c) :
    (smoothTotientCount X Y : ℝ) ≤
      (X : ℝ) * Real.exp
        (-(1 - c) * Real.log X +
          smoothPredecessorEulerLoss c₀ * smoothPredecessorPrimeRpowSum X Y c) := by
  calc
    (smoothTotientCount X Y : ℝ) ≤
        (X : ℝ) ^ c *
          Real.exp (smoothPredecessorEulerLoss c₀ * smoothPredecessorPrimeRpowSum X Y c) :=
      smoothTotientCount_le_rankinPrimeSum hc₀ hc
    _ = (X : ℝ) * Real.exp
        (-(1 - c) * Real.log X +
          smoothPredecessorEulerLoss c₀ * smoothPredecessorPrimeRpowSum X Y c) := by
      rw [rpow_eq_mul_exp_neg_one_sub hX, mul_assoc, ← Real.exp_add]

end

end RankAmplification
