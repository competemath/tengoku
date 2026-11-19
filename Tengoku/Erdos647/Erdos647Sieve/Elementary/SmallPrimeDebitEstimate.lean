/-
The fixed-constant lower bound for the EXACT protected smallPrimeDebit.
No imported Mertens or PNT theorem is used, and no estimate is assumed as a premise.
-/
import Tengoku.Erdos647.Erdos647Sieve.Specification
import Tengoku.Erdos647.Erdos647Sieve.Elementary.PrimeReciprocalLower

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
open scoped BigOperators Topology

noncomputable section
namespace Erdos647Sieve.Elementary

/-- The natural quotient loses less than one compared with real division.
@isnad1 id=le.1h2v.s5.f23f4206d322 from=translated src=- shape=d4d04bf9 vocab=b4a47039
-/
theorem nat_quotient_cast_lower (H p : ℕ) (hp : 0 < p) :
    (H : ℝ) / (p : ℝ) - 1 ≤ ((H / p : ℕ) : ℝ) := by
  have hi : H < (H / p + 1) * p :=
    (Nat.div_lt_iff_lt_mul hp).mp (Nat.lt_succ_self (H / p))
  have hr : (H : ℝ) < (((H / p : ℕ) : ℝ) + 1) * (p : ℝ) := by
    exact_mod_cast hi
  rw [sub_le_iff_le_add]
  apply (div_le_iff₀ (by exact_mod_cast hp : (0 : ℝ) < p)).mpr
  exact hr.le

/--
@isnad1 id=le.0h1v.s3.a8568a00863c from=translated src=- shape=9baae94e vocab=5a1e24e7
-/
theorem card_debitPrimes_le (H : ℕ) : (debitPrimes H).card ≤ H := by
  classical
  have hsub : debitPrimes H ⊆ Finset.Icc 1 H := by
    intro p hp
    have hi := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
    exact Finset.mem_Icc.mpr ⟨by omega, hi.2⟩
  simpa using Finset.card_le_card hsub

/-- Rounding is accounted for before applying the prime-count bound.
@isnad1 id=le.0h1v.s5.35f4c85d7432 from=translated src=- shape=30d67db9 vocab=6be5d1d6
-/
theorem smallPrimeDebit_ge_sum_sub_card (H : ℕ) :
    (H : ℝ) * (∑ p ∈ debitPrimes H, (p : ℝ)⁻¹) - ((debitPrimes H).card : ℝ) ≤
      (Erdos647Sieve.smallPrimeDebit H : ℝ) := by
  classical
  have hs := Finset.sum_le_sum (s := debitPrimes H)
    (f := fun p : ℕ => (H : ℝ) / (p : ℝ) - 1)
    (g := fun p : ℕ => ((H / p : ℕ) : ℝ)) (fun (p : ℕ) hp =>
      nat_quotient_cast_lower H p (Finset.mem_filter.mp hp).2.pos)
  simpa only [Erdos647Sieve.smallPrimeDebit, debitPrimes, Nat.cast_sum,
    Finset.sum_sub_distrib, div_eq_mul_inv, Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul, mul_one] using hs

/-- Mandatory small-prime debit, with the manuscript's exact -2 constant.
@isnad1 id=le.1h1v.s5.9d496f71e6c1 from=translated src=- shape=8f822deb vocab=907aa0ae
-/
theorem smallPrimeDebit_lower (H : ℕ) (hH : 2 ≤ H) :
    (H : ℝ) * (Real.log (Real.log (H : ℝ)) - 2) ≤
      (Erdos647Sieve.smallPrimeDebit H : ℝ) := by
  have hrec := mul_le_mul_of_nonneg_left (prime_reciprocal_lower H hH)
    (Nat.cast_nonneg H : (0 : ℝ) ≤ H)
  have hround := smallPrimeDebit_ge_sum_sub_card H
  have hcard : ((debitPrimes H).card : ℝ) ≤ (H : ℝ) := by
    exact_mod_cast card_debitPrimes_le H
  nlinarith

end Erdos647Sieve.Elementary
end
