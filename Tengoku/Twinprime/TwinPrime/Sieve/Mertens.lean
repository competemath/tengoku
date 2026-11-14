import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A Mertens-type upper bound from Chebyshev's `θ(x) ≤ x log 4`

Mathlib does not (yet) contain Mertens' theorems.  For the Brun sieve we only need an upper
bound of the right order, `∑_{p ≤ z} 1/p ≪ log log z`, and this follows from Chebyshev's
bound `θ(x) ≤ x log 4` by splitting the primes into dyadic blocks `(2^k, 2^{k+1}]`:

  `∑_{2^k < p ≤ 2^{k+1}} 1/p ≤ 2/((k+1) log 2) · 2^{-k} · θ(2^{k+1}) ≤ 8/(k+1)`,

so `∑_{p ≤ z} 1/p ≤ 8 H(⌊log₂ z⌋ + 1) ≤ 8 (1 + log (⌊log₂ z⌋ + 1))`
(`sum_primesLE_inv_le`).  The constant `8` is far from optimal (the truth is `1`).
-/

noncomputable section

open Finset Real Nat
open scoped Chebyshev

namespace TwinPrime.Sieve

/-- The dyadic block of primes `2^k < p ≤ 2^{k+1}`.-/
def primeBlock (k : ℕ) : Finset ℕ := (primesLE (2 ^ (k + 1))).filter fun p => 2 ^ k < p

theorem primesLE_two_pow_succ (k : ℕ) :
    primesLE (2 ^ (k + 1)) = primesLE (2 ^ k) ∪ primeBlock k := by
  ext p
  simp only [primeBlock, mem_union, mem_filter, mem_primesLE]
  constructor
  · rintro ⟨hp, hpp⟩
    rcases le_or_gt p (2 ^ k) with h | h
    · exact Or.inl ⟨h, hpp⟩
    · exact Or.inr ⟨⟨hp, hpp⟩, h⟩
  · rintro (⟨hp, hpp⟩ | ⟨⟨hp, hpp⟩, _⟩)
    · exact ⟨le_trans hp (Nat.pow_le_pow_right two_pos (Nat.le_succ k)), hpp⟩
    · exact ⟨hp, hpp⟩

theorem disjoint_primesLE_primeBlock (k : ℕ) : Disjoint (primesLE (2 ^ k)) (primeBlock k) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  rw [mem_primesLE] at hp
  simp only [primeBlock, mem_filter] at hq
  omega

/-- `log p ≥ (k+1) log 2 / 2` for `p` in the `k`-th block.-/
theorem log_ge_of_mem_primeBlock {k p : ℕ} (hp : p ∈ primeBlock k) :
    ((k : ℝ) + 1) * Real.log 2 / 2 ≤ Real.log p := by
  simp only [primeBlock, mem_filter, mem_primesLE] at hp
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hp1 : p ≤ 2 := by simpa using hp.1.1
    have hp2 : 2 ≤ p := hp.1.2.two_le
    have : p = 2 := by omega
    subst this
    simp
    linarith
  · have h1 : Real.log ((2 : ℝ) ^ k) ≤ Real.log p :=
      Real.log_le_log (by positivity) (by exact_mod_cast hp.2.le)
    rw [Real.log_pow] at h1
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith

/-- Block bound: `∑_{2^k < p ≤ 2^{k+1}} 1/p ≤ 8/(k+1)`.-/
theorem sum_primeBlock_inv_le (k : ℕ) :
    ∑ p ∈ primeBlock k, (p : ℝ)⁻¹ ≤ 8 / ((k : ℝ) + 1) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  -- each term: `1/p ≤ (2 / ((k+1) log 2)) * (log p / 2^k)`
  have hterm : ∀ p ∈ primeBlock k,
      (p : ℝ)⁻¹ ≤ 2 / (((k : ℝ) + 1) * Real.log 2) * (Real.log p / (2 : ℝ) ^ k) := by
    intro p hp
    have hlogp := log_ge_of_mem_primeBlock hp
    have hp2 : (2 : ℝ) ^ k < p := by
      simp only [primeBlock, mem_filter] at hp
      exact_mod_cast hp.2
    have hppos : (0 : ℝ) < p := lt_trans h2k hp2
    have hden : 0 < ((k : ℝ) + 1) * Real.log 2 * 2 ^ k := by positivity
    have hprod : 0 < ((k : ℝ) + 1) * Real.log 2 := mul_pos hk1 hlog2
    have key : ((k : ℝ) + 1) * Real.log 2 * 2 ^ k ≤ 2 * Real.log p * p := by
      have hlogp' : ((k : ℝ) + 1) * Real.log 2 ≤ 2 * Real.log p := by linarith
      calc ((k : ℝ) + 1) * Real.log 2 * 2 ^ k ≤ 2 * Real.log p * 2 ^ k :=
            mul_le_mul_of_nonneg_right hlogp' h2k.le
        _ ≤ 2 * Real.log p * p := mul_le_mul_of_nonneg_left hp2.le (by linarith)
    calc (p : ℝ)⁻¹ = 1 / p := inv_eq_one_div _
      _ ≤ (2 * Real.log p) / (((k : ℝ) + 1) * Real.log 2 * 2 ^ k) := by
          rw [div_le_div_iff₀ hppos hden]; linarith
      _ = 2 / (((k : ℝ) + 1) * Real.log 2) * (Real.log p / (2 : ℝ) ^ k) := by
          field_simp
  calc ∑ p ∈ primeBlock k, (p : ℝ)⁻¹
      ≤ ∑ p ∈ primeBlock k, 2 / (((k : ℝ) + 1) * Real.log 2) * (Real.log p / (2 : ℝ) ^ k) :=
        sum_le_sum hterm
    _ = 2 / (((k : ℝ) + 1) * Real.log 2) / (2 : ℝ) ^ k * ∑ p ∈ primeBlock k, Real.log p := by
        rw [mul_sum]
        apply sum_congr rfl
        intro p _
        ring
    _ ≤ 2 / (((k : ℝ) + 1) * Real.log 2) / (2 : ℝ) ^ k * θ (2 ^ (k + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [show (2 : ℝ) ^ (k + 1) = ((2 ^ (k + 1) : ℕ) : ℝ) by norm_num,
          Chebyshev.theta_eq_sum_primesLE_log]
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          simp only [primeBlock, mem_filter] at hp
          exact hp.1
        · intro p hp _
          exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt.le)
    _ ≤ 2 / (((k : ℝ) + 1) * Real.log 2) / (2 : ℝ) ^ k * (Real.log 4 * 2 ^ (k + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have := Chebyshev.theta_le_log4_mul_x (x := (2 : ℝ) ^ (k + 1)) (by positivity)
        exact this
    _ = 8 / ((k : ℝ) + 1) := by
        have h4 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        rw [h4]
        field_simp
        ring

/-- `∑_{p ≤ 2^{K+1}} 1/p ≤ 8 H(K+1)`.-/
theorem sum_primesLE_two_pow_inv_le (K : ℕ) :
    ∑ p ∈ primesLE (2 ^ (K + 1)), (p : ℝ)⁻¹ ≤ 8 * (harmonic (K + 1) : ℝ) := by
  induction K with
  | zero =>
    have : primesLE (2 ^ 1) = {2} := by decide
    rw [this, sum_singleton]
    simp [harmonic]
    norm_num
  | succ K ih =>
    rw [primesLE_two_pow_succ, sum_union (disjoint_primesLE_primeBlock _)]
    have hblock := sum_primeBlock_inv_le (K + 1)
    have hharm : (harmonic (K + 1 + 1) : ℝ) = harmonic (K + 1) + ((K + 1 + 1 : ℕ) : ℝ)⁻¹ := by
      rw [harmonic_succ]
      push_cast
      ring
    rw [hharm]
    push_cast at hblock ⊢
    have : (8 : ℝ) / ((K : ℝ) + 1 + 1) = 8 * ((K : ℝ) + 1 + 1)⁻¹ := by ring
    linarith

/-- **Mertens-type bound**: `∑_{p ≤ z} 1/p ≤ 8 (1 + log (⌊log₂ z⌋ + 1))`.-/
theorem sum_primesLE_inv_le (z : ℕ) :
    ∑ p ∈ primesLE z, (p : ℝ)⁻¹ ≤ 8 * (1 + Real.log ((Nat.log 2 z : ℝ) + 1)) := by
  set K := Nat.log 2 z with hK
  have hz : z ≤ 2 ^ (K + 1) := (Nat.lt_pow_succ_log_self one_lt_two z).le
  calc ∑ p ∈ primesLE z, (p : ℝ)⁻¹ ≤ ∑ p ∈ primesLE (2 ^ (K + 1)), (p : ℝ)⁻¹ := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          rw [mem_primesLE] at hp ⊢
          exact ⟨le_trans hp.1 hz, hp.2⟩
        · intros; positivity
    _ ≤ 8 * (harmonic (K + 1) : ℝ) := sum_primesLE_two_pow_inv_le K
    _ ≤ 8 * (1 + Real.log ((K : ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        have := harmonic_le_one_add_log (K + 1)
        push_cast at this
        exact this

end TwinPrime.Sieve
