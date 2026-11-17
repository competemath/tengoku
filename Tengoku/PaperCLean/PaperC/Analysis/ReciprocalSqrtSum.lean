import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.Seed.Data.Finset.Interval
import Lean.Elab.Tactic.Omega

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# An elementary reciprocal-square-root sum

This file records a deliberately elementary estimate used in the smooth-prime
part of Paper C.  It needs no information about the distribution of primes:
we simply enlarge a set of primes to all integers in the same interval.
-/

namespace PaperC

/-- The negative half power is the reciprocal of the square root.
@isnad1 id=eq.1h1v.s5.c51bc7d15409 from=translated src=- shape=0cce855d vocab=85c136b9
-/
lemma rpow_neg_one_half_eq_inv_sqrt (x : ℝ) (hx : 0 ≤ x) :
    x ^ (-(1 / 2 : ℝ)) = (Real.sqrt x)⁻¹ := by
  rw [Real.rpow_neg hx, ← Real.sqrt_eq_rpow]

/-- Taking square roots preserves the elementary inequality `n - 1 ≤ n`.
@isnad1 id=le.0h1v.s4.330a99ddeb0c from=translated src=- shape=b5af248d vocab=ea1e23b9
-/
lemma sqrt_nat_sub_one_le (n : ℕ) :
    Real.sqrt ((n - 1 : ℕ) : ℝ) ≤ Real.sqrt n :=
  Real.sqrt_le_sqrt (Nat.cast_le.mpr (Nat.sub_le n 1))

/-- Consecutive natural numbers have square-root squares differing by one.
@isnad1 id=eq.1h1v.s6.3c3e47a4626d from=translated src=- shape=f799f870 vocab=30b5e73a
-/
lemma sqrt_nat_sq_sub_sq_eq_one (n : ℕ) (hn : 1 ≤ n) :
    (Real.sqrt n) ^ 2 - (Real.sqrt ((n - 1 : ℕ) : ℝ)) ^ 2 = 1 := by
  rw [Real.sq_sqrt (Nat.cast_nonneg n),
    Real.sq_sqrt (Nat.cast_nonneg (n - 1)), Nat.cast_sub hn, Nat.cast_one]
  ring

/--
One reciprocal-square-root term is bounded by twice the corresponding
increment of the square-root function.
@isnad1 id=le.1h1v.s6.3a65b958cc0e from=translated src=- shape=9f5562a2 vocab=cb0c310c
-/
lemma inv_sqrt_nat_le_two_mul_sqrt_sub (n : ℕ) (hn : 1 ≤ n) :
    (Real.sqrt n)⁻¹ ≤
      2 * (Real.sqrt n - Real.sqrt ((n - 1 : ℕ) : ℝ)) := by
  have hsqrt : 0 < Real.sqrt n :=
    Real.sqrt_pos.2 (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))
  rw [inv_le_iff_one_le_mul₀' hsqrt]
  have hroot := sqrt_nat_sub_one_le n
  have hdiff_nonneg : 0 ≤ Real.sqrt n - Real.sqrt ((n - 1 : ℕ) : ℝ) :=
    sub_nonneg.mpr hroot
  have hsum : Real.sqrt n + Real.sqrt ((n - 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt n := by
    calc
      Real.sqrt n + Real.sqrt ((n - 1 : ℕ) : ℝ) ≤ Real.sqrt n + Real.sqrt n :=
        add_le_add_right hroot _
      _ = 2 * Real.sqrt n := (two_mul _).symm
  calc
    1 = (Real.sqrt n) ^ 2 - (Real.sqrt ((n - 1 : ℕ) : ℝ)) ^ 2 :=
      (sqrt_nat_sq_sub_sq_eq_one n hn).symm
    _ = (Real.sqrt n + Real.sqrt ((n - 1 : ℕ) : ℝ)) *
          (Real.sqrt n - Real.sqrt ((n - 1 : ℕ) : ℝ)) := sq_sub_sq _ _
    _ ≤ (Real.sqrt n - Real.sqrt ((n - 1 : ℕ) : ℝ)) * (2 * Real.sqrt n) :=
      (mul_le_mul_of_nonneg_right hsum hdiff_nonneg).trans_eq (mul_comm _ _)
    _ = Real.sqrt n * (2 * (Real.sqrt n - Real.sqrt ((n - 1 : ℕ) : ℝ))) := by
      ac_rfl

/--
The elementary bound

`∑_{1 ≤ n ≤ H} n⁻¹/² ≤ 2 √H`.

The proof is a finite telescoping argument, using
`n⁻¹/² ≤ 2 (√n - √(n-1))`.
@isnad1 id=le.0h1v.s6.71aed59ca115 from=translated src=- shape=ef21ac37 vocab=590ee6a4
-/
theorem sum_Icc_rpow_neg_one_half_le (H : ℕ) :
    (∑ n ∈ Finset.Icc 1 H, (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤
      2 * Real.sqrt H := by
  induction H with
  | zero => simp
  | succ H ih =>
      have hset :
          Finset.Icc 1 (H + 1) = insert (H + 1) (Finset.Icc 1 H) := by
        ext n
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnotmem : H + 1 ∉ Finset.Icc 1 H := by
        simp
      rw [hset, Finset.sum_insert hnotmem]
      rw [rpow_neg_one_half_eq_inv_sqrt _ (Nat.cast_nonneg _)]
      have hterm := inv_sqrt_nat_le_two_mul_sqrt_sub (H + 1) (by omega)
      simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] at hterm ⊢
      calc
        (Real.sqrt ((H : ℝ) + 1))⁻¹ +
              ∑ n ∈ Finset.Icc 1 H, (n : ℝ) ^ (-(1 / 2 : ℝ))
            ≤ (Real.sqrt ((H : ℝ) + 1))⁻¹ + 2 * Real.sqrt H :=
              add_le_add_right ih _
        _ ≤ 2 * (Real.sqrt ((H : ℝ) + 1) - Real.sqrt H) + 2 * Real.sqrt H :=
          add_le_add_left hterm _
        _ = 2 * Real.sqrt ((H : ℝ) + 1) := by ring

/-- The same estimate written with reciprocal square roots.
@isnad1 id=le.0h1v.s5.e5ec30e54780 from=translated src=- shape=e7ab1bd8 vocab=c862994e
-/
theorem sum_Icc_inv_sqrt_le (H : ℕ) :
    (∑ n ∈ Finset.Icc 1 H, (Real.sqrt n)⁻¹) ≤ 2 * Real.sqrt H := by
  simpa only [rpow_neg_one_half_eq_inv_sqrt _ (Nat.cast_nonneg _)] using
    sum_Icc_rpow_neg_one_half_le H

end PaperC
