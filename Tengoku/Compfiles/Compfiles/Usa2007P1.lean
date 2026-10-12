/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Tengoku

@[expose] public section

/-!
# USA Mathematical Olympiad 2007, Problem 1

Let n be a positive integer. Define a sequence by setting a₁ = n and,
for each k > 1, letting aₖ be the unique integer in the range 0 ≤ aₖ ≤ k - 1
for which a₁ + a₂ + ··· + aₖ is divisible by k. (For instance, when n = 9
the obtained sequence is 9, 1, 2, 0, 3, 3, 3, ....)
Prove that for any n the sequence a₁, a₂, ... eventually becomes constant.
-/

namespace Usa2007P1

/-- The partial sums `s n k = a n 0 + a n 1 + ... + a n k` of the sequence of the
problem, defined directly: `s n 0 = n`, and `s n (k + 1)` is the smallest multiple
of `k + 2` which is `≥ s n k`. -/
def s (n : ℕ) : ℕ → ℕ
  | 0 => n
  | (k + 1) => s n k + (k + 2 - s n k % (k + 2)) % (k + 2)

/-- The sequence of the problem, with indices shifted by one so that `a n 0 = n`:
for `k ≥ 1`, `a n k` is the unique integer in `[0, k]` for which `k + 1` divides
`s n k = a n 0 + ... + a n k`. -/
def a (n : ℕ) : ℕ → ℕ
  | 0 => n
  | (k + 1) => s n (k + 1) - s n k

-- sanity check against the example given in the problem statement
example : a 9 0 = 9 ∧ a 9 1 = 1 ∧ a 9 2 = 2 ∧ a 9 3 = 0 ∧ a 9 4 = 3 ∧
    a 9 5 = 3 ∧ a 9 6 = 3 := by
  decide

/--
@isnad1 id=eq.0h2v.s6.f3ecfbd997d0 from=translated src=- shape=05c2adb4 vocab=1ba9d946
-/
lemma s_succ (n k : ℕ) :
    s n (k + 1) = s n k + (k + 2 - s n k % (k + 2)) % (k + 2) := rfl

/--
@isnad1 id=eq.0h2v.s6.e69861bbdc69 from=translated src=- shape=833773b7 vocab=4551fdd6
-/
lemma a_succ (n k : ℕ) :
    a n (k + 1) = (k + 2 - s n k % (k + 2)) % (k + 2) :=
  Nat.add_sub_cancel_left _ _

/--
@isnad1 id=eq.0h2v.s5.3c9406576914 from=translated src=- shape=9522084e vocab=e14aad38
-/
lemma s_succ_eq_add_a (n k : ℕ) : s n (k + 1) = s n k + a n (k + 1) := by
  rw [a_succ, s_succ]

/--
@isnad1 id=lt.0h2v.s5.4b2d84770e3e from=translated src=- shape=aa0822b1 vocab=f6ce5463
-/
lemma a_succ_lt (n k : ℕ) : a n (k + 1) < k + 2 := by
  rw [a_succ]
  exact Nat.mod_lt _ (by lia)

/--
@isnad1 id=dvd.0h2v.s4.fe58399a4252 from=translated src=- shape=2337d3ac vocab=8c287a83
-/
lemma dvd_s (n k : ℕ) : (k + 1) ∣ s n k := by
  induction k with
  | zero => exact one_dvd n
  | succ k _ =>
      rw [Nat.dvd_iff_mod_eq_zero, s_succ, Nat.add_mod, Nat.mod_mod]
      generalize hr : s n k % (k + 2) = r
      have hrl : r < k + 2 := by rw [← hr]; exact Nat.mod_lt _ (by lia)
      rcases Nat.eq_zero_or_pos r with h0 | hpos
      · rw [h0]
        simp
      · rw [Nat.mod_eq_of_lt (by lia : k + 2 - r < k + 2),
            show r + (k + 2 - r) = k + 2 by lia]
        exact Nat.mod_self _

/-- The average `b n k = (a n 0 + ... + a n k) / (k + 1)`, a nonnegative integer. -/
def b (n k : ℕ) : ℕ := s n k / (k + 1)

/--
@isnad1 id=eq.0h2v.s5.dd0344fb280e from=translated src=- shape=0f2f19f5 vocab=a0117e76
-/
lemma s_eq (n k : ℕ) : s n k = (k + 1) * b n k := by
  show s n k = (k + 1) * (s n k / (k + 1))
  rw [mul_comm, Nat.div_mul_cancel (dvd_s n k)]

/--
@isnad1 id=le.0h2v.s4.39f633d0732d from=translated src=- shape=1f182b03 vocab=72b78449
-/
lemma b_succ_le (n k : ℕ) : b n (k + 1) ≤ b n k := by
  have h2 : s n (k + 1) = s n k + a n (k + 1) := s_succ_eq_add_a n k
  have h4 : a n (k + 1) < k + 2 := a_succ_lt n k
  have h5 : s n k = (k + 1) * b n k := s_eq n k
  have h6 : s n (k + 1) = (k + 2) * b n (k + 1) := s_eq n (k + 1)
  by_contra hlt
  have hlt' : b n k + 1 ≤ b n (k + 1) := not_le.mp hlt
  have h7 : (k + 2) * (b n k + 1) ≤ (k + 2) * b n (k + 1) :=
    Nat.mul_le_mul_left _ hlt'
  rw [show (k + 2) * (b n k + 1) = (k + 1) * b n k + b n k + (k + 2) by ring] at h7
  lia

/--
@isnad1 id=ex.0h1v.s4.84e3cd7e2f6b from=translated src=- shape=1b19a6f7 vocab=833b92b0
-/
lemma b_eventually_const (n : ℕ) : ∃ N, ∀ k ≥ N, b n k = b n N := by
  have hb : Antitone (b n) := antitone_nat_of_succ_le (b_succ_le n)
  obtain ⟨N, hN⟩ := Nat.sInf_mem (Set.range_nonempty (b n))
  refine ⟨N, fun k hk => le_antisymm (hb hk) ?_⟩
  rw [hN]
  exact Nat.sInf_le ⟨k, rfl⟩

/-- The partial sums of `a n` are indeed given by `s n`.
@isnad1 id=eq.0h2v.s5.b732f3f50a38 from=translated src=- shape=8d6447ec vocab=9702a629
-/
lemma sum_a (n k : ℕ) : ∑ i ∈ Finset.range (k + 1), a n i = s n k := by
  induction k with
  | zero => rw [Finset.sum_range_one]; rfl
  | succ k ih =>
      rw [Finset.sum_range_succ, ih, s_succ_eq_add_a]

/-- `a n` satisfies the divisibility requirement of the problem statement.
@isnad1 id=dvd.0h2v.s5.debf80618457 from=translated src=- shape=c0694b84 vocab=93b60901
-/
lemma dvd_sum_a (n k : ℕ) : (k + 1) ∣ ∑ i ∈ Finset.range (k + 1), a n i := by
  rw [sum_a]
  exact dvd_s n k

/-- `a n` satisfies the range requirement of the problem statement.
@isnad1 id=le.1h2v.s4.3947d28bd7e5 from=translated src=- shape=cbd56e08 vocab=9628a1cc
-/
lemma a_le (n : ℕ) {k : ℕ} (hk : 1 ≤ k) : a n k ≤ k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by lia)
  exact Nat.lt_succ_iff.mp (a_succ_lt n j)

end Usa2007P1
