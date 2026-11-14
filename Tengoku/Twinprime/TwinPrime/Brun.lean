import Tengoku
import Tengoku.Twinprime.TwinPrime.Basic
import Tengoku.Twinprime.TwinPrime.Sieve.TwinBound

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Brun's theorem

From the explicit sieve bound `twinCount_le_explicit` with the choice `z = ⌊x^{1/4}⌋` we derive

* `twinCount_le` : `π₂(x) ≤ 2^33 · x / (log x)^2` for all `x ≥ 2`;
* `twinCount_isBigO` : `π₂(x) = O(x / (log x)^2)`;
* `brun` : **Brun's theorem** — the sum of the reciprocals of the twin primes converges,
  in the two forms `Summable (Set.indicator twinPrimes fun n => 1/n)` and
  `Summable (fun p : twinPrimes => 1/p)`.

This is the strongest known upper-bound information about twin primes of this elementary type,
and it is the natural formal counterpart of the fact that twin primes are rare (density zero).
The constant `2^33` is far from optimal; no attempt is made to optimise it.
-/

noncomputable section

open Finset Real Nat
open scoped Topology

namespace TwinPrime

open Sieve

/-! ### Real-analysis helpers -/

theorem log_le_sixteen_mul_rpow {x : ℝ} (hx : 0 ≤ x) :
    Real.log x ≤ 16 * x ^ (1 / 16 : ℝ) := by
  calc Real.log x ≤ x ^ (1 / 16 : ℝ) / (1 / 16) := Real.log_le_rpow_div hx (by norm_num)
    _ = 16 * x ^ (1 / 16 : ℝ) := by ring

theorem log_pow_eight_le {x : ℝ} (hx : 1 ≤ x) :
    (Real.log x) ^ 8 ≤ 2 ^ 32 * Real.sqrt x := by
  have hx0 : 0 ≤ x := by linarith
  calc (Real.log x) ^ 8 ≤ (16 * x ^ (1 / 16 : ℝ)) ^ 8 :=
        pow_le_pow_left₀ (Real.log_nonneg hx) (log_le_sixteen_mul_rpow hx0) 8
    _ = 16 ^ 8 * (x ^ (1 / 16 : ℝ)) ^ (8 : ℕ) := by rw [mul_pow]
    _ = 2 ^ 32 * x ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast (x ^ (1 / 16 : ℝ)) 8, ← Real.rpow_mul hx0]
        norm_num
    _ = 2 ^ 32 * Real.sqrt x := by rw [Real.sqrt_eq_rpow]

theorem log_sq_le {x : ℝ} (hx : 1 ≤ x) :
    (Real.log x) ^ 2 ≤ 2 ^ 8 * x ^ (1 / 8 : ℝ) := by
  have hx0 : 0 ≤ x := by linarith
  calc (Real.log x) ^ 2 ≤ (16 * x ^ (1 / 16 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (Real.log_nonneg hx) (log_le_sixteen_mul_rpow hx0) 2
    _ = 16 ^ 2 * (x ^ (1 / 16 : ℝ)) ^ (2 : ℕ) := by rw [mul_pow]
    _ = 2 ^ 8 * x ^ (1 / 8 : ℝ) := by
        rw [← Real.rpow_natCast (x ^ (1 / 16 : ℝ)) 2, ← Real.rpow_mul hx0]
        norm_num

/-! ### The parameter `z = ⌊x^{1/4}⌋` -/

/-- Fourth root (floor).-/
def z4 (x : ℕ) : ℕ := Nat.sqrt (Nat.sqrt x)

theorem z4_pow_four_le (x : ℕ) : z4 x ^ 4 ≤ x := by
  unfold z4
  calc Nat.sqrt (Nat.sqrt x) ^ 4 = (Nat.sqrt (Nat.sqrt x) ^ 2) ^ 2 := by ring
    _ ≤ (Nat.sqrt x) ^ 2 := Nat.pow_le_pow_left (Nat.sqrt_le' _) 2
    _ ≤ x := Nat.sqrt_le' x

theorem lt_z4_add_one_pow_four (x : ℕ) : x < (z4 x + 1) ^ 4 := by
  unfold z4
  have h1 : x < (Nat.sqrt x + 1) ^ 2 := Nat.lt_succ_sqrt' x
  have h2 : Nat.sqrt x < (Nat.sqrt (Nat.sqrt x) + 1) ^ 2 := Nat.lt_succ_sqrt' _
  calc x < (Nat.sqrt x + 1) ^ 2 := h1
    _ ≤ ((Nat.sqrt (Nat.sqrt x) + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left h2 2
    _ = (Nat.sqrt (Nat.sqrt x) + 1) ^ 4 := by ring

theorem sixteen_le_z4 {x : ℕ} (hx : 2 ^ 16 ≤ x) : 16 ≤ z4 x := by
  unfold z4
  rw [Nat.le_sqrt]
  rw [Nat.le_sqrt]
  omega

theorem z4_sq_le_sqrt (x : ℕ) : ((z4 x : ℝ)) ^ 2 ≤ Real.sqrt x := by
  unfold z4
  calc ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ) ^ 2 = ((Nat.sqrt (Nat.sqrt x) ^ 2 : ℕ) : ℝ) := by
        push_cast; ring
    _ ≤ ((Nat.sqrt x : ℕ) : ℝ) := by exact_mod_cast Nat.sqrt_le' _
    _ ≤ Real.sqrt x := Real.nat_sqrt_le_real_sqrt

/-- `log z ≥ ¼ log x − log 2` for `z = z4 x`, `x ≥ 1`.-/
theorem log_z4_ge {x : ℕ} (hx : 1 ≤ x) :
    (1 / 4 : ℝ) * Real.log x - Real.log 2 ≤ Real.log (z4 x) := by
  have hz1 : 1 ≤ z4 x := by
    unfold z4; rw [Nat.le_sqrt, Nat.le_sqrt]; omega
  have hzpos : (0 : ℝ) < z4 x := by exact_mod_cast hz1
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have h1 : Real.log x < 4 * Real.log ((z4 x : ℝ) + 1) := by
    have : Real.log x < Real.log (((z4 x : ℝ) + 1) ^ 4) := by
      apply Real.log_lt_log hxpos
      exact_mod_cast lt_z4_add_one_pow_four x
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have h2 : Real.log ((z4 x : ℝ) + 1) ≤ Real.log 2 + Real.log (z4 x) := by
    rw [← Real.log_mul (by norm_num) hzpos.ne']
    apply Real.log_le_log (by positivity)
    have : (1 : ℝ) ≤ z4 x := by exact_mod_cast hz1
    linarith
  linarith

/-- `z + 1 ≤ 2 x^{1/4}` for `z = z4 x`.-/
theorem z4_add_one_le {x : ℕ} (hx : 1 ≤ x) :
    ((z4 x : ℝ) + 1) ≤ 2 * (x : ℝ) ^ (1 / 4 : ℝ) := by
  have hz1 : (1 : ℝ) ≤ z4 x := by
    have : 1 ≤ z4 x := by unfold z4; rw [Nat.le_sqrt, Nat.le_sqrt]; omega
    exact_mod_cast this
  have hz : (z4 x : ℝ) ≤ (x : ℝ) ^ (1 / 4 : ℝ) := by
    have h4 : ((z4 x : ℝ) ^ (4 : ℕ)) ≤ (x : ℝ) := by exact_mod_cast z4_pow_four_le x
    calc (z4 x : ℝ) = (((z4 x : ℝ) ^ (4 : ℕ)) ^ ((4 : ℕ) : ℝ)⁻¹) := by
          rw [Real.pow_rpow_inv_natCast (by positivity) (by norm_num)]
      _ ≤ (x : ℝ) ^ ((4 : ℕ) : ℝ)⁻¹ :=
          Real.rpow_le_rpow (by positivity) h4 (by positivity)
      _ = (x : ℝ) ^ (1 / 4 : ℝ) := by norm_num
  linarith

/-! ### The bound `π₂(x) ≤ 2^33 x / (log x)^2` -/

/-! ### Brun's theorem -/

/-- The summand `1/n` on twin primes, `0` elsewhere.-/
def twinRecip (n : ℕ) : ℝ := Set.indicator twinPrimes (fun n : ℕ => (n : ℝ)⁻¹) n

theorem twinRecip_nonneg (n : ℕ) : 0 ≤ twinRecip n := by
  unfold twinRecip
  apply Set.indicator_nonneg
  intro n _
  positivity

theorem twinRecip_zero : twinRecip 0 = 0 := by
  unfold twinRecip
  rw [Set.indicator_of_notMem]
  intro h
  exact Nat.not_prime_zero h.1

/-- Dyadic decomposition of a partial sum.-/
theorem sum_range_two_pow_le (a : ℕ → ℝ) (B : ℕ → ℝ)
    (hblock : ∀ k, ∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), a n ≤ B k) (K : ℕ) :
    ∑ n ∈ range (2 ^ K), a n ≤ a 0 + ∑ k ∈ range K, B k := by
  induction K with
  | zero => simp
  | succ K ih =>
    have h1 : 2 ^ K ≤ 2 ^ (K + 1) := Nat.pow_le_pow_right two_pos (Nat.le_succ K)
    rw [range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le (2 ^ K)) h1, ← range_eq_Ico,
      sum_range_succ]
    linarith [hblock K]

/-- The block `[2^k, 2^{k+1})` contributes at most `π₂(2^{k+1}) / 2^k`.-/
theorem twinRecip_block_le (k : ℕ) :
    ∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), twinRecip n ≤ (twinCount (2 ^ (k + 1)) : ℝ) / 2 ^ k := by
  classical
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  calc ∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), twinRecip n
      = ∑ n ∈ (Ico (2 ^ k) (2 ^ (k + 1))).filter (· ∈ twinPrimes), (n : ℝ)⁻¹ := by
        rw [sum_filter]
        apply sum_congr rfl
        intro n _
        unfold twinRecip
        rw [Set.indicator_apply]
    _ ≤ ∑ n ∈ (Ico (2 ^ k) (2 ^ (k + 1))).filter (· ∈ twinPrimes), ((2 : ℝ) ^ k)⁻¹ := by
        apply sum_le_sum
        intro n hn
        rw [mem_filter, mem_Ico] at hn
        apply inv_anti₀ hpos
        exact_mod_cast hn.1.1
    _ = #((Ico (2 ^ k) (2 ^ (k + 1))).filter (· ∈ twinPrimes)) * ((2 : ℝ) ^ k)⁻¹ := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (twinCount (2 ^ (k + 1)) : ℝ) * ((2 : ℝ) ^ k)⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        unfold twinCount
        apply Nat.cast_le.mpr
        apply card_le_card
        intro n hn
        rw [mem_filter, mem_Ico] at hn
        rw [mem_filter, mem_range]
        exact ⟨by omega, hn.2⟩
    _ = (twinCount (2 ^ (k + 1)) : ℝ) / 2 ^ k := by rw [div_eq_mul_inv]

/-- `∑_{k < K} 1/(k+1)^2 ≤ 2`.-/
theorem sum_inv_sq_succ_le (K : ℕ) : ∑ k ∈ range K, (((k + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤ 2 := by
  have h := sum_Ioo_inv_sq_le (α := ℝ) 0 (K + 1)
  simp only [Nat.cast_zero, zero_add, div_one] at h
  have himg : (range K).image (fun k => k + 1) = Ioo 0 (K + 1) := by
    ext i
    simp only [mem_image, mem_range, mem_Ioo]
    constructor
    · rintro ⟨k, hk, rfl⟩; omega
    · intro hi; exact ⟨i - 1, by omega, by omega⟩
  rw [← himg, sum_image (fun a _ b _ h => Nat.succ_injective h)] at h
  exact h

end TwinPrime
