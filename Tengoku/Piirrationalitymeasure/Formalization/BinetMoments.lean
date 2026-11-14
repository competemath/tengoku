import Tengoku.Piirrationalitymeasure.Formalization.BinetKernel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The Bernoulli moments of the positive Binet partial fractions. -/

namespace PiIrrationality

noncomputable def binetPole (n : ℕ) : ℝ := 2 * Real.pi * ((n : ℝ) + 1)

theorem binetPole_pos (n : ℕ) : 0 < binetPole n := by
  unfold binetPole
  positivity

noncomputable def positiveBernoulliCoeff (m : ℕ) : ℝ :=
  (-1) ^ (m + 1) * (bernoulli (2 * m) : ℝ) / ((2 * m).factorial : ℝ)

theorem hasSum_binetMoment {m : ℕ} (hm : 0 < m) :
    HasSum (fun n : ℕ => 2 / binetPole n ^ (2 * m)) (positiveBernoulliCoeff m) := by
  have hz := hasSum_zeta_nat hm.ne'
  have hshift : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (2 * m))
      ((-1 : ℝ) ^ (m + 1) * 2 ^ (2 * m - 1) * Real.pi ^ (2 * m) *
        (bernoulli (2 * m) : ℝ) / ((2 * m).factorial : ℝ)) := by
    have h := hz.summable.sum_add_tsum_nat_add 1
    rw [hz.tsum_eq] at h
    have hs := (summable_nat_add_iff 1).mpr hz.summable
    have hzero : (2 * m : ℕ) ≠ 0 := by omega
    simp only [Finset.sum_range_one, Nat.cast_zero, zero_pow hzero, div_zero,
      zero_add, Nat.cast_add, Nat.cast_one] at h
    simpa only [Nat.cast_add, Nat.cast_one, h] using hs.hasSum
  have hpow : (2 : ℝ) ^ (2 * m - 1) * 2 = 2 ^ (2 * m) := by
    rw [← pow_succ]
    congr 1
    omega
  have h := hshift.mul_left (2 / (2 * Real.pi) ^ (2 * m))
  convert! h using 1
  · funext n
    unfold binetPole
    rw [mul_pow]
    ring
  · unfold positiveBernoulliCoeff
    rw [mul_pow]
    field_simp
    rw [← hpow]
    ring

theorem positiveBernoulliCoeff_pos {m : ℕ} (hm : 0 < m) :
    0 < positiveBernoulliCoeff m := by
  have hs := hasSum_binetMoment hm
  rw [← hs.tsum_eq]
  exact hs.summable.tsum_pos (fun n => by positivity [binetPole_pos n]) 0
    (by positivity [binetPole_pos 0])

theorem positiveBernoulliCoeff_eq_abs {m : ℕ} (hm : 0 < m) :
    positiveBernoulliCoeff m = |(bernoulli (2 * m) : ℝ)| / ((2 * m).factorial : ℝ) := by
  calc
    positiveBernoulliCoeff m = |positiveBernoulliCoeff m| :=
      (abs_of_pos (positiveBernoulliCoeff_pos hm)).symm
    _ = _ := by simp [positiveBernoulliCoeff, abs_div, abs_mul]

theorem signed_positiveBernoulliCoeff (m : ℕ) :
    (-1 : ℝ) ^ m * positiveBernoulliCoeff (m + 1) =
      (bernoulli (2 * (m + 1)) : ℝ) / ((2 * (m + 1)).factorial : ℝ) := by
  have hs : (-1 : ℝ) ^ m * (-1 : ℝ) ^ (m + 1 + 1) = 1 := by
    rw [← pow_add]
    have he : m + (m + 1 + 1) = 2 * (m + 1) := by omega
    rw [he, pow_mul]
    norm_num
  unfold positiveBernoulliCoeff
  rw [← mul_div_assoc, ← mul_assoc, hs, one_mul]

end PiIrrationality
