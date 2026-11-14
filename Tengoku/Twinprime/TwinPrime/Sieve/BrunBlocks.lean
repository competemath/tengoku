import Tengoku
import Tengoku.Twinprime.TwinPrime.Sieve.BrunHooleyBounds
import Tengoku.Twinprime.TwinPrime.Sieve.Mertens
import Tengoku.Twinprime.TwinPrime.Sieve.BrunLower

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Blocks of primes by iterated square roots

For Brun's sieve on the twin sequence we split the primes `p ≤ z` into blocks
`(t_{i+1}, t_i]`, `t_0 = z`, `t_{i+1} = ⌊√t_i⌋`, `i < r := ⌊log₂ log₂ z⌋ + 1`, so that
`t_r ≤ 1` and every prime `≤ z` lies in exactly one block.  Key properties:

* `thr_le_rpow`: `t_i ≤ z^{1/2^i}` (so the block products have bounded total exponent);
* `sum_block_inv_le`: `∑_{p ∈ block i} 1/p ≤ 16` uniformly in `i` (from the dyadic Mertens
  bound), hence `∑_{p ∈ block i} ν p ≤ 32`;
* `brunBlocks z : Blocks (primorial z) r`.
-/

noncomputable section

open Finset Real Nat ArithmeticFunction
open scoped ArithmeticFunction.omega

namespace TwinPrime.Sieve

/-! ### Thresholds -/

/-- Iterated square roots: `thr z 0 = z`, `thr z (i+1) = ⌊√(thr z i)⌋`.-/
def thr (z : ℕ) : ℕ → ℕ
  | 0 => z
  | i + 1 => Nat.sqrt (thr z i)

@[simp] theorem thr_zero (z : ℕ) : thr z 0 = z := rfl
@[simp] theorem thr_succ (z i : ℕ) : thr z (i + 1) = Nat.sqrt (thr z i) := rfl

theorem thr_succ_le (z i : ℕ) : thr z (i + 1) ≤ thr z i := Nat.sqrt_le_self _

theorem thr_antitone (z : ℕ) : Antitone (thr z) :=
  antitone_nat_of_succ_le (thr_succ_le z)

theorem one_le_thr {z : ℕ} (hz : 1 ≤ z) (i : ℕ) : 1 ≤ thr z i := by
  induction i with
  | zero => simpa using hz
  | succ i ih =>
    rw [thr_succ, Nat.le_sqrt]
    simpa using ih

/-- `thr z i < 2^{2^{m-i}}` whenever `z < 2^{2^m}` and `i ≤ m`.-/
theorem thr_lt_two_pow {z m : ℕ} (hz : z < 2 ^ (2 ^ m)) :
    ∀ i, i ≤ m → thr z i < 2 ^ (2 ^ (m - i)) := by
  intro i
  induction i with
  | zero => intro _; simpa using hz
  | succ i ih =>
    intro hi
    have h := ih (by omega)
    rw [thr_succ, Nat.sqrt_lt']
    calc thr z i < 2 ^ (2 ^ (m - i)) := h
      _ = (2 ^ (2 ^ (m - (i + 1)))) ^ 2 := by
          rw [← pow_mul]
          congr 1
          have : m - i = (m - (i + 1)) + 1 := by omega
          rw [this, pow_succ]

/-- The number of blocks.-/
def nBlocks (z : ℕ) : ℕ := Nat.log 2 (Nat.log 2 z) + 1

theorem lt_two_pow_two_pow_nBlocks (z : ℕ) : z < 2 ^ (2 ^ nBlocks z) := by
  unfold nBlocks
  have h1 : Nat.log 2 z < 2 ^ (Nat.log 2 (Nat.log 2 z) + 1) := Nat.lt_pow_succ_log_self one_lt_two _
  have h2 : z < 2 ^ (Nat.log 2 z + 1) := Nat.lt_pow_succ_log_self one_lt_two z
  calc z < 2 ^ (Nat.log 2 z + 1) := h2
    _ ≤ 2 ^ (2 ^ (Nat.log 2 (Nat.log 2 z) + 1)) := Nat.pow_le_pow_right two_pos (by omega)

/-- The last threshold is at most `1`.-/
theorem thr_nBlocks_le_one (z : ℕ) : thr z (nBlocks z) ≤ 1 := by
  have := thr_lt_two_pow (lt_two_pow_two_pow_nBlocks z) (nBlocks z) le_rfl
  simp at this
  omega

theorem one_le_nBlocks (z : ℕ) : 1 ≤ nBlocks z := by unfold nBlocks; omega

/-- `thr z i ≤ z^{1/2^i}` as real numbers.-/
theorem thr_le_rpow {z : ℕ} (hz : 1 ≤ z) (i : ℕ) :
    (thr z i : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 2 ^ i) := by
  have hzr : (1 : ℝ) ≤ z := by exact_mod_cast hz
  induction i with
  | zero => simp
  | succ i ih =>
    rw [thr_succ]
    calc (Nat.sqrt (thr z i) : ℝ) ≤ Real.sqrt (thr z i) := Real.nat_sqrt_le_real_sqrt
      _ ≤ Real.sqrt ((z : ℝ) ^ ((1 : ℝ) / 2 ^ i)) := Real.sqrt_le_sqrt ih
      _ = (z : ℝ) ^ ((1 : ℝ) / 2 ^ (i + 1)) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith)]
          congr 1
          rw [pow_succ]
          field_simp

/-! ### Block index of a prime -/

/-- The block index of `p`: the largest `i ≤ r - 1` with `p ≤ thr z i`.-/
def bidx (z p : ℕ) : ℕ := Nat.findGreatest (fun i => p ≤ thr z i) (nBlocks z - 1)

theorem bidx_le (z p : ℕ) : bidx z p ≤ nBlocks z - 1 := Nat.findGreatest_le _

theorem bidx_lt (z p : ℕ) : bidx z p < nBlocks z := by
  have := bidx_le z p
  have := one_le_nBlocks z
  omega

theorem le_thr_bidx {z p : ℕ} (hp : p ≤ z) : p ≤ thr z (bidx z p) :=
  Nat.findGreatest_spec (P := fun i => p ≤ thr z i) (Nat.zero_le _) (by simpa using hp)

theorem thr_bidx_succ_lt {z p : ℕ} (hp2 : 2 ≤ p) : thr z (bidx z p + 1) < p := by
  by_cases h : bidx z p + 1 ≤ nBlocks z - 1
  · have := Nat.findGreatest_is_greatest (P := fun i => p ≤ thr z i)
      (Nat.lt_succ_self (bidx z p)) h
    simpa using this
  · have hb : bidx z p + 1 = nBlocks z := by
      have := bidx_le z p; have := one_le_nBlocks z; omega
    rw [hb]
    have := thr_nBlocks_le_one z
    omega

/-- The block index as an element of `Fin (nBlocks z)`.-/
def bidxFin (z p : ℕ) : Fin (nBlocks z) := ⟨bidx z p, bidx_lt z p⟩

/-- The set of primes in block `i`.-/
def blockPrimes (z : ℕ) (i : Fin (nBlocks z)) : Finset ℕ :=
  (primesLE z).filter fun p => bidxFin z p = i

theorem mem_blockPrimes {z : ℕ} {i : Fin (nBlocks z)} {p : ℕ} :
    p ∈ blockPrimes z i ↔ (p ≤ z ∧ p.Prime) ∧ bidxFin z p = i := by
  unfold blockPrimes
  rw [mem_filter, mem_primesLE]

theorem prime_of_mem_blockPrimes {z : ℕ} {i : Fin (nBlocks z)} {p : ℕ} (hp : p ∈ blockPrimes z i) :
    p.Prime := (mem_blockPrimes.mp hp).1.2

/-- Primes in block `i` lie in `(thr z (i+1), thr z i]`.-/
theorem thr_lt_of_mem_blockPrimes {z : ℕ} {i : Fin (nBlocks z)} {p : ℕ}
    (hp : p ∈ blockPrimes z i) : thr z (i + 1) < p ∧ p ≤ thr z i := by
  rw [mem_blockPrimes] at hp
  have hi : bidx z p = i := by
    have := hp.2
    unfold bidxFin at this
    exact congrArg Fin.val this
  rw [← hi]
  exact ⟨thr_bidx_succ_lt hp.1.2.two_le, le_thr_bidx hp.1.1⟩

/-! ### The blocks -/

/-- Block `i`: the product of the primes in `(thr z (i+1), thr z i]`.-/
def brunBlock (z : ℕ) (i : Fin (nBlocks z)) : ℕ := ∏ p ∈ blockPrimes z i, p

theorem brunBlock_dvd_primorial (z : ℕ) (i : Fin (nBlocks z)) :
    brunBlock z i ∣ primorial z := by
  rw [primorial_eq_prod_primesLE]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)

theorem brunBlock_squarefree (z : ℕ) (i : Fin (nBlocks z)) : Squarefree (brunBlock z i) :=
  (squarefree_primorial z).squarefree_of_dvd (brunBlock_dvd_primorial z i)

theorem primeFactors_brunBlock (z : ℕ) (i : Fin (nBlocks z)) :
    (brunBlock z i).primeFactors = blockPrimes z i :=
  Nat.primeFactors_prod fun _p hp => prime_of_mem_blockPrimes hp

theorem brunBlock_coprime (z : ℕ) (i j : Fin (nBlocks z)) (hij : i ≠ j) :
    Nat.Coprime (brunBlock z i) (brunBlock z j) := by
  unfold brunBlock
  apply Nat.Coprime.prod_left
  intro p hp
  apply Nat.Coprime.prod_right
  intro q hq
  rw [Nat.coprime_primes (prime_of_mem_blockPrimes hp) (prime_of_mem_blockPrimes hq)]
  intro hpq
  subst hpq
  rw [mem_blockPrimes] at hp hq
  exact hij (hp.2.symm.trans hq.2)

theorem prod_brunBlock (z : ℕ) : ∏ i, brunBlock z i = primorial z := by
  unfold brunBlock blockPrimes
  rw [primorial_eq_prod_primesLE]
  exact Finset.prod_fiberwise_of_maps_to (fun p _ => mem_univ (bidxFin z p)) _

/-- The block decomposition of `primorial z`.-/
def brunBlocks (z : ℕ) : Blocks (primorial z) (nBlocks z) where
  block := brunBlock z
  block_squarefree := brunBlock_squarefree z
  block_coprime := brunBlock_coprime z
  prod_block := prod_brunBlock z

/-! ### The prime sum in a block is bounded -/

/-- For `2^a < p ≤ 2^{b+1}` (i.e. `Nat.log 2 (p-1) ∈ [a, b]`), the sum `∑ 1/p` over the primes
in a set `S` with that property is at most `∑_{k=a}^{b} 8/(k+1)`.-/
theorem sum_inv_le_of_log_range (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (a b : ℕ)
    (hab : ∀ p ∈ S, a ≤ Nat.log 2 (p - 1) ∧ Nat.log 2 (p - 1) ≤ b) :
    ∑ p ∈ S, (p : ℝ)⁻¹ ≤ ∑ k ∈ Finset.Icc a b, 8 / ((k : ℝ) + 1) := by
  classical
  rw [← sum_fiberwise_of_maps_to (g := fun p => Nat.log 2 (p - 1)) (t := Finset.Icc a b)
    (fun p hp => by rw [mem_Icc]; exact hab p hp)]
  apply sum_le_sum
  intro k _
  refine le_trans ?_ (sum_primeBlock_inv_le k)
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rw [mem_filter] at hp
    have hpp := hS p hp.1
    have hp2 := hpp.two_le
    unfold primeBlock
    rw [mem_filter, mem_primesLE]
    have h1 : 2 ^ k ≤ p - 1 := by rw [← hp.2]; exact Nat.pow_log_le_self 2 (by omega)
    have h2 : p - 1 < 2 ^ (k + 1) := by rw [← hp.2]; exact Nat.lt_pow_succ_log_self one_lt_two _
    exact ⟨⟨by omega, hpp⟩, by omega⟩
  · intro p _ _
    positivity

/-- `∑_{k=q}^{2q+1} 8/(k+1) ≤ 16` (a block of dyadic scales spanning one doubling).-/
theorem sum_Icc_inv_le (q K : ℕ) (hK : K ≤ 2 * q + 1) :
    ∑ k ∈ Finset.Icc q K, 8 / ((k : ℝ) + 1) ≤ 16 := by
  calc ∑ k ∈ Finset.Icc q K, 8 / ((k : ℝ) + 1) ≤ ∑ _k ∈ Finset.Icc q K, 8 / ((q : ℝ) + 1) := by
        apply sum_le_sum
        intro k hk
        rw [mem_Icc] at hk
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        have : (q : ℝ) ≤ k := by exact_mod_cast hk.1
        linarith
    _ = #(Finset.Icc q K) * (8 / ((q : ℝ) + 1)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (2 * (q : ℝ) + 2) * (8 / ((q : ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [Nat.card_Icc]
        have : K + 1 - q ≤ 2 * q + 2 := by omega
        exact_mod_cast this
    _ = 16 := by field_simp; ring

/-- `∑_{p ∈ block i} 1/p ≤ 16`.-/
theorem sum_blockPrimes_inv_le {z : ℕ} (hz : 1 ≤ z) (i : Fin (nBlocks z)) :
    ∑ p ∈ blockPrimes z i, (p : ℝ)⁻¹ ≤ 16 := by
  set t := thr z i with ht
  set K := Nat.log 2 t with hK
  have ht1 : 1 ≤ t := one_le_thr hz i
  have hsqrt : 2 ^ (K / 2) ≤ Nat.sqrt t := by
    rw [Nat.le_sqrt, ← pow_add]
    calc 2 ^ (K / 2 + K / 2) ≤ 2 ^ K := Nat.pow_le_pow_right two_pos (by omega)
      _ ≤ t := Nat.pow_log_le_self 2 (by omega)
  refine le_trans (sum_inv_le_of_log_range (blockPrimes z i) (fun p hp => prime_of_mem_blockPrimes hp)
    (K / 2) K ?_) (sum_Icc_inv_le (K / 2) K (by omega))
  intro p hp
  obtain ⟨hlo, hhi⟩ := thr_lt_of_mem_blockPrimes hp
  have hp2 := (prime_of_mem_blockPrimes hp).two_le
  rw [thr_succ] at hlo
  rw [← ht] at hlo hhi
  constructor
  · -- `2^{K/2} ≤ sqrt t < p`, so `2^{K/2} ≤ p - 1`, so `K/2 ≤ log₂ (p-1)`
    apply Nat.le_log_of_pow_le one_lt_two
    omega
  · -- `p - 1 ≤ t`, so `log₂ (p-1) ≤ K`
    exact Nat.log_mono_right (by omega)

/-- `∑_{p ∈ block i} ν p ≤ 32` for `ν p ≤ 2/p`.-/
theorem sum_blockPrimes_twinNu2_le {z : ℕ} (hz : 1 ≤ z) (i : Fin (nBlocks z)) :
    ∑ p ∈ blockPrimes z i, twinNu2 p ≤ 32 := by
  calc ∑ p ∈ blockPrimes z i, twinNu2 p ≤ ∑ p ∈ blockPrimes z i, 2 * (p : ℝ)⁻¹ := by
        apply sum_le_sum
        intro p hp
        rw [mul_comm, ← div_eq_inv_mul]
        exact twinNu2_prime_le (prime_of_mem_blockPrimes hp)
    _ = 2 * ∑ p ∈ blockPrimes z i, (p : ℝ)⁻¹ := by rw [mul_sum]
    _ ≤ 2 * 16 := mul_le_mul_of_nonneg_left (sum_blockPrimes_inv_le hz i) (by norm_num)
    _ = 32 := by norm_num

theorem card_blockPrimes_le {z : ℕ} (i : Fin (nBlocks z)) : #(blockPrimes z i) ≤ thr z i + 1 := by
  calc #(blockPrimes z i) ≤ #(range (thr z i + 1)) := by
        apply card_le_card
        intro p hp
        have := (thr_lt_of_mem_blockPrimes hp).2
        rw [mem_range]
        omega
    _ = thr z i + 1 := card_range _

end TwinPrime.Sieve
