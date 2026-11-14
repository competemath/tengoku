import Tengoku.Piirrationalitymeasure.Formalization.CoefficientSeries

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Analytic sums of the actual rational generating series throughout the unit disk. -/

namespace PiIrrationality

open PowerSeries

section SeriesSums

variable {K : Type*} [RCLike K]

theorem ratSeries_hasSum_C (c : ℚ) (z : K) :
    HasSum (fun k => (↑(coeff k (C c)) : K) * z ^ k) (c : K) := by
  convert! hasSum_ite_eq (0 : ℕ) (c : K) using 1
  ext k
  by_cases hk : k = 0 <;> simp [coeff_C, hk]

theorem ratSeries_hasSum_natCast (m : ℕ) (z : K) :
    HasSum (fun k => (↑(coeff k (m : PowerSeries ℚ)) : K) * z ^ k) (m : K) := by
  simpa only [map_natCast, Rat.cast_natCast] using ratSeries_hasSum_C (m : ℚ) z

theorem ratSeries_hasSum_X (z : K) :
    HasSum (fun k => (↑(coeff k (X : PowerSeries ℚ)) : K) * z ^ k) z := by
  convert! hasSum_ite_eq (1 : ℕ) z using 1
  ext k
  by_cases hk : k = 1 <;> simp [coeff_X, hk]

theorem ratSeries_hasSum_add {f g : PowerSeries ℚ} {z u v : K}
    (hf : HasSum (fun k => (↑(coeff k f) : K) * z ^ k) u)
    (hg : HasSum (fun k => (↑(coeff k g) : K) * z ^ k) v) :
    HasSum (fun k => (↑(coeff k (f + g)) : K) * z ^ k) (u + v) := by
  simpa only [map_add, Rat.cast_add, add_mul] using hf.add hg

theorem ratSeries_hasSum_mul {f g : PowerSeries ℚ} {z u v : K}
    (hf : HasSum (fun k => (↑(coeff k f) : K) * z ^ k) u)
    (hg : HasSum (fun k => (↑(coeff k g) : K) * z ^ k) v) :
    HasSum (fun k => (↑(coeff k (f * g)) : K) * z ^ k) (u * v) := by
  have hfn := summable_norm_iff.mpr hf.summable
  have hgn := summable_norm_iff.mpr hg.summable
  have h := (summable_norm_sum_mul_antidiagonal_of_summable_norm hfn hgn).of_norm.hasSum
  rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hgn,
    hf.tsum_eq, hg.tsum_eq] at h
  convert! h using 1
  ext k
  rw [coeff_mul, Rat.cast_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Rat.cast_mul, mul_mul_mul_comm, ← pow_add,
    Finset.HasAntidiagonal.mem_antidiagonal.mp hp]

theorem ratSeries_hasSum_pow {f : PowerSeries ℚ} {z u : K}
    (hf : HasSum (fun k => (↑(coeff k f) : K) * z ^ k) u) (n : ℕ) :
    HasSum (fun k => (↑(coeff k (f ^ n)) : K) * z ^ k) (u ^ n) := by
  induction n with
  | zero => simpa only [pow_zero, Nat.cast_one] using ratSeries_hasSum_natCast 1 z
  | succ n ih => simpa only [pow_succ] using ratSeries_hasSum_mul ih hf

theorem PSeries_hasSum (z : K) :
    HasSum (fun k => (↑(coeff k PSeries) : K) * z ^ k)
      (2 + 6 * z + 9 * z ^ 2 + 6 * z ^ 3 + 2 * z ^ 4) := by
  have hX := ratSeries_hasSum_X z
  have h2 := ratSeries_hasSum_natCast 2 z
  have h6 := ratSeries_hasSum_natCast 6 z
  have h9 := ratSeries_hasSum_natCast 9 z
  exact ratSeries_hasSum_add
    (ratSeries_hasSum_add
      (ratSeries_hasSum_add
        (ratSeries_hasSum_add h2 (ratSeries_hasSum_mul h6 hX))
        (ratSeries_hasSum_mul h9 (ratSeries_hasSum_pow hX 2)))
      (ratSeries_hasSum_mul h6 (ratSeries_hasSum_pow hX 3)))
    (ratSeries_hasSum_mul h2 (ratSeries_hasSum_pow hX 4))

theorem SNumerator_hasSum (z : K) :
    HasSum (fun k => (↑(coeff k SNumerator) : K) * z ^ k)
      ((1 + z) ^ 3714 * (2 + 6 * z + 9 * z ^ 2 + 6 * z ^ 3 + 2 * z ^ 4) ^ 3714) := by
  rw [SNumerator_eq]
  have h1 : HasSum (fun k => (↑(coeff k (1 : PowerSeries ℚ)) : K) * z ^ k) 1 := by
    simpa only [Nat.cast_one] using ratSeries_hasSum_natCast 1 z
  exact ratSeries_hasSum_mul
    (ratSeries_hasSum_pow
      (ratSeries_hasSum_add h1 (ratSeries_hasSum_X z)) 3714)
    (ratSeries_hasSum_pow (PSeries_hasSum z) 3714)

theorem inversePower_hasSum {z : K} (hz : ‖z‖ < 1) {d : ℕ} (hd : 0 < d) :
    HasSum (fun k => (↑(coeff k (invOneSubPow ℚ d).val) : K) * z ^ k)
      (1 / (1 - z) ^ d) := by
  have h := hasSum_choose_mul_geometric_of_norm_lt_one (d - 1) hz
  simpa only [invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos ℚ d hd,
    coeff_mk, Rat.cast_natCast, Nat.sub_add_cancel hd, Nat.add_comm (d - 1)] using h

theorem Sseries_hasSum {z : K} (hz : ‖z‖ < 1) :
    HasSum (fun k => (↑(coeff k Sseries) : K) * z ^ k)
      ((1 + z) ^ 3714 * (2 + 6 * z + 9 * z ^ 2 + 6 * z ^ 3 + 2 * z ^ 4) ^ 3714 /
        (1 - z) ^ 7430) := by
  simpa only [Sseries, div_eq_mul_inv, one_mul] using
    ratSeries_hasSum_mul (SNumerator_hasSum z) (inversePower_hasSum hz (by norm_num : 0 < 7430))

end SeriesSums

theorem Sseries_hasSum_real {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun k => (↑(coeff k Sseries) : ℝ) * x ^ k) (SReal x) := by
  have hx : ‖x‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hx0] using hx1
  simpa only [SReal, PReal] using Sseries_hasSum hx

theorem Sseries_pow_hasSum_real {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    HasSum (fun k => (↑(coeff k (Sseries ^ n)) : ℝ) * x ^ k) (SReal x ^ n) :=
  ratSeries_hasSum_pow (Sseries_hasSum_real hx0 hx1) n

end PiIrrationality
