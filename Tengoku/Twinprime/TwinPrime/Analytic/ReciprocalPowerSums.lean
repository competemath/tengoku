import Tengoku.Seed.Analysis.SumIntegralComparisons
import Tengoku.Seed.Analysis.SpecialFunctions.Integrals.Basic
import Tengoku.Seed.Algebra.Order.Floor.Semifield

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite sums of reciprocal powers

An integral comparison on `[1,N]`, with the first term separated, gives
the exact constant `1 / (1 - α)` for `0 ≤ α < 1`. Real cutoffs are floored
only in the finite sum. The zero cutoff and exponent zero are included.
-/

noncomputable section

open Finset

namespace TwinPrime.Analytic

/--
@isnad1 id=le.2h2v.s6.71329053762d from=translated src=- shape=04c177a2 vocab=1c652f2b
-/
theorem sum_Ioc_rpow_neg_le (N : ℕ) (α : ℝ) (hα : 0 ≤ α) (hα1 : α < 1) :
    (∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-α)) ≤ (N : ℝ) ^ (1 - α) / (1 - α) := by
  by_cases hN : N = 0
  · subst N
    simp [Real.zero_rpow (by linarith : 1 - α ≠ 0)]
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-α)) (Set.Icc (1 : ℝ) N) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have hi := AntitoneOn.sum_le_integral_Ico (f := fun x : ℝ => x ^ (-α)) hN1
    (by simpa only [Nat.cast_one] using hanti)
  simp only [Nat.cast_one] at hi
  have heq : (∑ n ∈ Ioc 1 N, (n : ℝ) ^ (-α)) =
      ∑ n ∈ Ico 1 N, ((n + 1 : ℕ) : ℝ) ^ (-α) := by
    rw [sum_Ico_add' (fun n : ℕ => (n : ℝ) ^ (-α)) 1 N (c := 1)]
    congr 1
  have hsum := sum_Ioc_consecutive (fun n : ℕ => (n : ℝ) ^ (-α))
    (show 0 ≤ 1 by omega) hN1
  have hfirst : (∑ n ∈ Ioc 0 (1 : ℕ), (n : ℝ) ^ (-α)) = 1 := by simp
  rw [hfirst] at hsum
  have hint : (∫ x : ℝ in (1 : ℝ)..N, x ^ (-α)) =
      ((N : ℝ) ^ (1 - α) - 1) / (1 - α) := by
    rw [integral_rpow (Or.inl (by linarith : -1 < -α))]
    rw [show -α + 1 = 1 - α by ring, Real.one_rpow]
  rw [hint, ← heq] at hi
  have hd : 0 < 1 - α := by linarith
  calc
    _ = 1 + ∑ n ∈ Ioc 1 N, (n : ℝ) ^ (-α) := hsum.symm
    _ ≤ 1 + ((N : ℝ) ^ (1 - α) - 1) / (1 - α) := add_le_add le_rfl hi
    _ ≤ _ := by
      apply (le_div_iff₀ hd).mpr
      field_simp
      linarith

/--
@isnad1 id=le.3h2v.s6.dcaa97c76db2 from=translated src=- shape=100a4214 vocab=42977d57
-/
theorem sum_Ioc_natFloor_rpow_neg_le (x : ℝ) (hx : 0 ≤ x)
    (α : ℝ) (hα : 0 ≤ α) (hα1 : α < 1) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, (n : ℝ) ^ (-α)) ≤ x ^ (1 - α) / (1 - α) := by
  apply (sum_Ioc_rpow_neg_le ⌊x⌋₊ α hα hα1).trans
  exact div_le_div_of_nonneg_right
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hx) (by linarith)) (by linarith)

/--
@isnad1 id=le.1h1v.s6.08273e19bb26 from=translated src=- shape=95609d2c vocab=4260ba39
-/
theorem sum_Ioc_natFloor_one_div_sqrt_le (x : ℝ) (hx : 0 ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, 1 / Real.sqrt (n : ℝ)) ≤ 2 * Real.sqrt x := by
  have h := sum_Ioc_natFloor_rpow_neg_le x hx (1 / 2) (by norm_num) (by norm_num)
  norm_num only [show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num] at h
  simp_rw [Real.rpow_neg (Nat.cast_nonneg _), ← Real.sqrt_eq_rpow] at h
  convert h using 1 <;> norm_num [div_eq_mul_inv, mul_comm]

/--
@isnad1 id=le.0h1v.s5.bded66cc872a from=translated src=- shape=e5ed4a91 vocab=eb76f83a
-/
theorem sum_Ioc_one_div_sqrt_le (N : ℕ) :
    (∑ n ∈ Ioc 0 N, 1 / Real.sqrt (n : ℝ)) ≤ 2 * Real.sqrt (N : ℝ) := by
  simpa only [Nat.floor_natCast] using
    sum_Ioc_natFloor_one_div_sqrt_le (N : ℝ) (Nat.cast_nonneg N)

end TwinPrime.Analytic
