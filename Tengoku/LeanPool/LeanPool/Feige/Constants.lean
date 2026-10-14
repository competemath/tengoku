/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import Tengoku

/-!
# The sharp finite-dimensional constant

This file records the elementary real-analysis facts about

`bₙ,₁ = (n / (n + 1))ⁿ`

which is the `δ = 1` value of the second branch in (1.1).  The
probability-theoretic proof is kept in later modules.
-/

@[expose] public section

namespace Feige

open Filter Topology

/-- The unit-slack sharp constant `bₙ,₁` in dimension `n`. -/
noncomputable def sharpConstant (n : ℕ) : ℝ :=
  ((n : ℝ) / (n + 1)) ^ n

/--
@isnad1 id=eq.0h0v.s3.062ff480bed7 from=translated src=- shape=1ac31801 vocab=492ad340
-/
@[simp] theorem sharpConstant_zero : sharpConstant 0 = 1 := by
  simp [sharpConstant]

/-- The sharp constant is positive in every dimension, including dimension zero.
@isnad1 id=lt.0h1v.s3.ef1764b3ad4b from=translated src=- shape=b9369acb vocab=f349ea12
-/
theorem sharpConstant_pos (n : ℕ) : 0 < sharpConstant n := by
  cases n with
  | zero => simp
  | succ n =>
      simp only [sharpConstant]
      positivity

/-- The sharp constant is nonnegative.
@isnad1 id=le.0h1v.s3.e75cd15f1258 from=translated src=- shape=b9369acb vocab=afd6d015
-/
theorem sharpConstant_nonneg (n : ℕ) : 0 ≤ sharpConstant n :=
  (sharpConstant_pos n).le

/-- The sharp constant is at most one.
@isnad1 id=le.0h1v.s3.b87eae8d80c0 from=translated src=- shape=a311c14d vocab=afd6d015
-/
theorem sharpConstant_le_one (n : ℕ) : sharpConstant n ≤ 1 := by
  simp only [sharpConstant]
  apply pow_le_one₀
  · positivity
  · exact (div_le_one (by positivity)).2 (by norm_num)

/-- For positive `n`, the sharp constant is the reciprocal of the standard
sequence converging to `exp 1`. -/
private theorem sharpConstant_eq_inv (n : ℕ) (hn : n ≠ 0) :
    sharpConstant n = ((1 + (1 : ℝ) / n) ^ n)⁻¹ := by
  rw [sharpConstant, ← inv_pow]
  congr 1
  field_simp

/-- The finite-dimensional sharp constant is strictly larger than `exp (-1)`.
@isnad1 id=lt.1h1v.s4.d991b5b7beb8 from=translated src=- shape=87f2a3f7 vocab=cafb00fe
-/
theorem exp_neg_one_lt_sharpConstant {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (-1) < sharpConstant n := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hbase :
      (1 + (1 : ℝ) / n) ^ n < (Real.exp ((1 : ℝ) / n)) ^ n := by
    apply pow_lt_pow_left₀
    · simpa [add_comm] using Real.add_one_lt_exp (one_div_ne_zero hnR.ne')
    · positivity
    · exact hn0
  have hexp : (Real.exp ((1 : ℝ) / n)) ^ n = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [sharpConstant_eq_inv n hn0, Real.exp_neg]
  apply inv_lt_inv₀ (Real.exp_pos 1) (by positivity) |>.2
  exact hbase.trans_eq hexp

/-- The finite-dimensional sharp constants converge to `exp (-1)`.
@isnad1 id=tendsto.0h0v.s4.860828075e85 from=translated src=- shape=3772a883 vocab=b0766522
-/
theorem tendsto_sharpConstant :
    Tendsto sharpConstant atTop (𝓝 (Real.exp (-1))) := by
  have h :=
    (Real.tendsto_one_add_div_pow_exp 1).inv₀ (Real.exp_ne_zero 1)
  rw [← Real.exp_neg] at h
  apply h.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact (sharpConstant_eq_inv n hn).symm

end Feige
