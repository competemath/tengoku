/-
Small arithmetic interfaces for dyadic cycle-length arguments.

This file contains no graph-theoretic assumptions and does not assert the
Erdos-64 conjecture.
-/

import Tengoku
import Tengoku.Erdos64.Erdos64.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

/-- A power of two with exponent at least two is at least four.-/
theorem four_le_pow_two {k : ℕ} (hk : 2 ≤ k) : 4 ≤ 2 ^ k := by
  cases k with
  | zero => omega
  | succ k =>
    cases k with
    | zero => omega
    | succ k =>
      rw [Nat.pow_succ]
      have hpos : 0 < 2 ^ (Nat.succ k) := by positivity
      omega

/-- Every positive natural number lies in a half-open dyadic interval.-/
theorem exists_pow_two_le_and_lt_succ_pow_two {n : ℕ} (hn : 0 < n) :
    ∃ k : ℕ, 2 ^ k ≤ n ∧ n < 2 ^ (k + 1) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hnzero : n = 0
    · subst n
      exact ⟨0, by norm_num, by norm_num⟩
    · obtain ⟨k, hlo, hhi⟩ := ih (Nat.pos_of_ne_zero hnzero)
      by_cases hnext : n + 1 < 2 ^ (k + 1)
      · exact ⟨k, by omega, hnext⟩
      · have heq : n + 1 = 2 ^ (k + 1) := by omega
        refine ⟨k + 1, ?_, ?_⟩
        · exact heq.ge
        · calc
            n + 1 = 2 ^ (k + 1) := heq
            _ < 2 ^ (k + 1) * 2 := by
              have hpos : 0 < 2 ^ (k + 1) := by positivity
              omega
            _ = 2 ^ (k + 1 + 1) := (Nat.pow_succ 2 (k + 1)).symm

/-- A sufficiently long unit-step interval contains a target dyadic length.-/
theorem exists_dyadic_point_of_interval
    {m M : ℕ} (hm : 0 < m) (hM : 4 ≤ M) (hreaches : 2 * m ≤ M) :
    ∃ k t : ℕ, 2 ≤ k ∧
      m + t = 2 ^ k ∧ m + t ≤ M := by
  by_cases hm4 : 4 ≤ m
  · obtain ⟨k, hlo, hhi⟩ :=
      exists_pow_two_le_and_lt_succ_pow_two hm
    have hk : 2 ≤ k := by
      by_contra hk'
      have hklt : k < 2 := by omega
      interval_cases k <;> norm_num at hhi <;> omega
    have hmnext : m ≤ 2 ^ (k + 1) := by omega
    have hnext_le : 2 ^ (k + 1) ≤ M := by
      calc
        2 ^ (k + 1) = 2 ^ k * 2 := by rw [Nat.pow_succ]
        _ ≤ m * 2 := Nat.mul_le_mul_right 2 hlo
        _ = 2 * m := by omega
        _ ≤ M := hreaches
    refine ⟨k + 1, 2 ^ (k + 1) - m, ?_, ?_, ?_⟩
    · omega
    · exact Nat.add_sub_of_le hmnext
    · rw [Nat.add_sub_of_le hmnext]
      exact hnext_le
  · have hm_le : m ≤ 4 := by omega
    refine ⟨2, 4 - m, by omega, ?_, ?_⟩
    · exact Nat.add_sub_of_le hm_le
    · rw [Nat.add_sub_of_le hm_le]
      exact hM

/-- A seven-entry arithmetic record for the two-ear cycle lengths.-/
structure SevenLengthArithmetic where
  n : ℕ
  p : ℕ
  q : ℕ
  alpha : ℕ
  beta : ℕ
  gamma : ℕ
  delta : ℕ

/-- The seven cycle-length expressions associated with a two-ear record.-/
def SevenLengthArithmetic.lengths (s : SevenLengthArithmetic) : Finset ℕ :=
  {s.n,
    s.p + s.alpha + s.beta,
    s.p + s.gamma + s.delta,
    s.q + s.beta + s.gamma,
    s.q + s.delta + s.alpha,
    s.p + s.q + s.gamma + s.alpha,
    s.p + s.q + s.beta + s.delta}

/-- Membership in `lengths` exposes the seven entries explicitly.-/
theorem SevenLengthArithmetic.mem_lengths_iff
    (s : SevenLengthArithmetic) (x : ℕ) :
    x ∈ s.lengths ↔
      x = s.n ∨
      x = s.p + s.alpha + s.beta ∨
      x = s.p + s.gamma + s.delta ∨
      x = s.q + s.beta + s.gamma ∨
      x = s.q + s.delta + s.alpha ∨
      x = s.p + s.q + s.gamma + s.alpha ∨
      x = s.p + s.q + s.beta + s.delta := by
  simp [SevenLengthArithmetic.lengths, or_comm]

/-- A dyadic member of the seven-entry record identifies one of its entries.-/
theorem SevenLengthArithmetic.exists_dyadic_entry
    (s : SevenLengthArithmetic)
    (h : ∃ k : ℕ, 2 ≤ k ∧ 2 ^ k ∈ s.lengths) :
    ∃ k : ℕ, 2 ≤ k ∧
      (s.n = 2 ^ k ∨
        s.p + s.alpha + s.beta = 2 ^ k ∨
        s.p + s.gamma + s.delta = 2 ^ k ∨
        s.q + s.beta + s.gamma = 2 ^ k ∨
        s.q + s.delta + s.alpha = 2 ^ k ∨
        s.p + s.q + s.gamma + s.alpha = 2 ^ k ∨
        s.p + s.q + s.beta + s.delta = 2 ^ k) := by
  obtain ⟨k, hk, hm⟩ := h
  have hm' := (s.mem_lengths_iff (2 ^ k)).mp hm
  refine ⟨k, hk, ?_⟩
  rcases hm' with h | h | h | h | h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr (Or.inl h.symm))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h.symm)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h.symm))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h.symm)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h.symm)))))

/- A realized arithmetic step and one dyadic point produce the graph target. -/
theorem hasPowerOfTwoCycle_of_realized_step
    {V : Type u} {G : SimpleGraph V}
    {m g M : ℕ}
    (hrealize :
      ∀ t : ℕ, m + g * t ≤ M →
        HasSimpleCycleOfLength G (m + g * t))
    (hdyadic :
      ∃ k t : ℕ, 2 ≤ k ∧
        m + g * t = 2 ^ k ∧ m + g * t ≤ M) :
    HasPowerOfTwoCycle G := by
  obtain ⟨k, t, hk, hlength, hbound⟩ := hdyadic
  exact hasPowerOfTwoCycle_of_simpleCycleOfLength
    (hrealize t hbound) hk hlength

/-- A dyadic target in the realized range, together with the exact residue
condition, yields a step parameter.-/
theorem exists_step_of_dyadic_residue
    {m g M k : ℕ}
    (hk : 2 ≤ k)
    (hlo : m ≤ 2 ^ k)
    (hhi : 2 ^ k ≤ M)
    (hres : g ∣ 2 ^ k - m) :
    ∃ t : ℕ, m + g * t = 2 ^ k ∧ m + g * t ≤ M := by
  rcases hres with ⟨t, ht⟩
  refine ⟨t, ?_, ?_⟩
  · omega
  · omega

/-- The graph target follows from a dyadic value satisfying the exact
residue condition for the realized arithmetic progression.-/
theorem hasPowerOfTwoCycle_of_realized_step_of_residue
    {V : Type u} {G : SimpleGraph V}
    {m g M : ℕ}
    (hrealize :
      ∀ t : ℕ, m + g * t ≤ M →
        HasSimpleCycleOfLength G (m + g * t))
    (hdyadic :
      ∃ k : ℕ, 2 ≤ k ∧ m ≤ 2 ^ k ∧ 2 ^ k ≤ M ∧
        g ∣ 2 ^ k - m) :
    HasPowerOfTwoCycle G := by
  obtain ⟨k, hk, hlo, hhi, hres⟩ := hdyadic
  obtain ⟨t, hlength, hbound⟩ :=
    exists_step_of_dyadic_residue hk hlo hhi hres
  exact hasPowerOfTwoCycle_of_realized_step hrealize
    ⟨k, t, hk, hlength, hbound⟩

end Erdos64
