/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import Tengoku

/-!
# IMO 2006 N3

For each positive integer $n$, define
$$ f(n) = \frac{1}{n} \sum_{k = 1}^n \left\lfloor \frac{n}{k} \right\rfloor. $$
1. Prove that $f(n + 1) > f(n)$ infinitely often.
2. Prove that $f(n + 1) < f(n)$ infinitely often.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2006SL.pdf).
Throughout the code documentation, `d` denotes the divisor function.
-/

@[expose] public section

namespace IMOSL
namespace IMO2006N3

open Finset

/-- The function `f(n) = 1/n ∑_{k ≤ n} ⌊n/k⌋`. -/
def f (n : ℕ) : Rat := Rat.divInt ((∑ k ∈ Icc 1 n, n / k : ℕ) : ℤ) n

/-- The formula `∑_{k ≤ n} ⌊n/k⌋ = ∑_{k ≤ n} d(k)`.
@isnad1 id=eq.0h1v.s5.dfa06e4e7023 from=translated src=- shape=982b6939 vocab=3bac2580
-/
theorem sum_div_eq_sum_card_divisors (n : ℕ) :
    ∑ k ∈ Icc 1 n, n / k = ∑ k ∈ Icc 1 n, #k.divisors := by
  ---- Proceed by induction.
  induction n with | zero => rfl | succ n n_ih => ?_
  ---- We only need to check `∑_{k ≤ n + 1} ⌊(n + 1)/k⌋ = ∑_{k ≤ n} ⌊n/k⌋ + d(n + 1)`.
  calc ∑ k ∈ Icc 1 (n + 1), (n + 1) / k
    _ = ∑ k ∈ Icc 1 (n + 1), (n / k + if k ∣ n + 1 then 1 else 0) :=
      sum_congr rfl λ _ _ ↦ Nat.succ_div
    _ = ∑ k ∈ Icc 1 (n + 1), n / k + ∑ k ∈ Icc 1 (n + 1), if k ∣ n + 1 then 1 else 0 :=
      sum_add_distrib
    _ = ∑ k ∈ Icc 1 n, n / k + #{k ∈ Icc 1 (n + 1) | k ∣ n + 1} := by
      refine congrArg₂ _ ?_ (card_filter (· ∣ n + 1) _).symm
      rw [sum_Icc_succ_top n.succ_pos, Nat.div_eq_of_lt n.lt_succ_self, Nat.add_zero]
    _ = ∑ k ∈ Icc 1 (n + 1), #k.divisors := by
      rw [n_ih, sum_Icc_succ_top n.succ_pos, ← Ico_succ_right_eq_Icc]; rfl

/-- If `m ∑_{k ≤ n} d(k) < n ∑_{k ≤ m} d(k)`, then `f(n) < f(m)`.
@isnad1 id=lt.1h2v.s6.2dc330333f7d from=translated src=- shape=167a7b65 vocab=457ba133
-/
theorem f_lt_f_of_sum_div
    {m n : ℕ} (h : m * ∑ k ∈ Icc 1 n, #k.divisors < n * ∑ k ∈ Icc 1 m, #k.divisors) :
    f n < f m := by
  ---- Both `m = 0` and `n = 0` contradicts the assumption.
  obtain rfl | hm : m = 0 ∨ 0 < m := Nat.eq_zero_or_pos m
  · rw [Nat.zero_mul, Icc_eq_empty_of_lt Nat.one_pos, sum_empty, Nat.mul_zero] at h
    exact absurd rfl h.ne
  obtain rfl | hn : n = 0 ∨ 0 < n := Nat.eq_zero_or_pos n
  · rw [Nat.zero_mul, Icc_eq_empty_of_lt Nat.one_pos, sum_empty, Nat.mul_zero] at h
    exact absurd rfl h.ne
  ---- The rest follows from the property of `f` and the rationals.
  unfold f
  replace hm : 0 < (m : ℤ) := Nat.cast_pos.mpr hm
  replace hn : 0 < (n : ℤ) := Nat.cast_pos.mpr hn
  rwa [← Rat.not_le, Rat.divInt_le_divInt hm hn, ← Int.natCast_mul, ← Int.natCast_mul,
    Int.not_le, Nat.cast_lt, sum_div_eq_sum_card_divisors, sum_div_eq_sum_card_divisors,
    Nat.mul_comm, Nat.mul_comm _ n]

/-! ### Part 1 -/

/-- Let `g : ℕ → ℕ` be an unbounded function.
  Then there exists infinitely many `n` such that `g(k) < g(n)` for all `k < n`.
@isnad1 id=ex.1h2v.s5.efc646a76f6c from=translated src=- shape=636e8a68 vocab=590c6ac3
-/
theorem exists_infinite_map_lt_of_lt_of_unbounded {g : ℕ → ℕ} (hg : ∀ M, ∃ n, M < g n) (N) :
    ∃ n ≥ N, ∀ k < n, g k < g n := by
  ---- If all such `n` are `≤ N`, then all values of `g` are at most `max{g(k) : k ≤ N}`.
  contrapose! hg
  refine ⟨(range (N + 1)).sup' nonempty_range_add_one g, λ n ↦ ?_⟩
  ---- The previous statement follows by strong induction on `n`.
  induction n using Nat.strong_induction_on with | h n n_ih => ?_
  obtain hn | hn : n ≤ N ∨ n ≥ N := Nat.le_total _ _
  · exact le_sup' _ (mem_range_succ_iff.mpr hn)
  · obtain ⟨k, hk, hk0⟩ : ∃ k < n, g n ≤ g k := hg _ hn
    exact hk0.trans (n_ih k hk)

/-- There exists infinitely many `n` such that `d(k) < d(n)` for all `k < n`.
@isnad1 id=ex.0h1v.s4.3dc92e7fcd9d from=translated src=- shape=c5f7c992 vocab=97ebf5d5
-/
theorem exists_infinite_card_divisors_lt_of_lt (N : ℕ) :
    ∃ n ≥ N, ∀ k < n, #k.divisors < #n.divisors :=
  have h (M) : ∃ n : ℕ, M < #n.divisors := by
    refine ⟨2 ^ M, ?_⟩
    rw [Nat.divisors_prime_pow Nat.prime_two, card_map, card_range]
    exact Nat.lt_add_one M
  exists_infinite_map_lt_of_lt_of_unbounded h N

/-- If `n > 1` and `d(k) < d(n)` for all `k < n`, then `f(n - 1) < f(n)`.
@isnad1 id=lt.2h1v.s5.ca0c5c5d6b6a from=translated src=- shape=dcc9680b vocab=a5b3b144
-/
theorem f_pred_lt_of_card_divisors (hn : n > 0) (hn0 : ∀ k < n, #k.divisors < #n.divisors) :
    f (n - 1) < f n := by
  ---- The case `n = 1` follows by how division is defined in Lean.
  obtain rfl | hn1 : 1 = n ∨ 1 < n := Nat.eq_or_lt_of_le hn
  · decide
  ---- The case `n > 1` follows in the normal way.
  refine f_lt_f_of_sum_div ?_
  have hn2 : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn
  calc n * ∑ k ∈ Icc 1 (n - 1), #k.divisors
    _ = (n - 1) * ∑ k ∈ Icc 1 (n - 1), #k.divisors + ∑ k ∈ Icc 1 (n - 1), #k.divisors := by
      rw [← Nat.add_one_mul, hn2]
    _ < (n - 1) * ∑ k ∈ Icc 1 (n - 1), #k.divisors + ∑ k ∈ Icc 1 (n - 1), #n.divisors :=
      Nat.add_lt_add_left (k := _) <| sum_lt_sum_of_nonempty
        ⟨1, left_mem_Icc.mpr (Nat.le_pred_of_lt hn1)⟩
        (λ k hk ↦ hn0 _ (Nat.lt_of_le_pred hn (mem_Icc.mp hk).2))
    _ = (n - 1) * ∑ k ∈ Icc 1 (n - 1), #k.divisors + (n - 1) * #(n - 1 + 1).divisors := by
      rw [hn2, sum_const, Nat.card_Icc, hn2]; rfl
    _ = (n - 1) * ∑ k ∈ Icc 1 n, #k.divisors := by
      rw [← Nat.mul_add, ← sum_Icc_succ_top (Nat.succ_pos _), hn2]

/-- Final solution, part 1
@isnad1 id=ex.0h1v.s4.1fa0aec11e8b from=translated src=- shape=f6438ca2 vocab=4d705f65
-/
theorem final_solution_part1 (N : ℕ) : ∃ n ≥ N, f n < f (n + 1) := by
  ---- Pick some `t > N` such that `d(k) < d(t)` for all `k < t`.
  obtain ⟨t, ht, ht0⟩ : ∃ t > N, ∀ k < t, #k.divisors < #t.divisors :=
    exists_infinite_card_divisors_lt_of_lt _
  ---- Then `n = t - 1` works.
  refine ⟨t - 1, Nat.le_pred_of_lt ht, ?_⟩
  have ht1 : t > 0 := Nat.zero_lt_of_lt ht
  calc f (t - 1)
    _ < f t := f_pred_lt_of_card_divisors ht1 ht0
    _ = f (t - 1 + 1) := congrArg f (Nat.succ_pred_eq_of_pos ht1).symm

/-! ### Part 2 -/

/-- For `n > 1`, we have `d(n) > 1`.
@isnad1 id=lt.1h1v.s4.a7928c861060 from=translated src=- shape=2b5cef4b vocab=75fba90f
-/
theorem one_lt_card_divisors {n : ℕ} (hn : n > 1) : #n.divisors > 1 := calc
  1 < #n.properDivisors + 1 :=
    Nat.lt_add_of_pos_left (card_pos.mpr ⟨1, Nat.one_mem_properDivisors_iff_one_lt.mpr hn⟩)
  _ = #(insert n n.properDivisors) :=
    (card_insert_of_notMem Nat.self_notMem_properDivisors).symm
  _ = #n.divisors := congrArg card (Nat.insert_self_properDivisors (Nat.ne_zero_of_lt hn))

/-- For `n ≥ 6`, we have `∑_{k ≤ n} d(k) > 2n`.
@isnad1 id=lt.1h1v.s5.6b799991bba9 from=translated src=- shape=d6ab3f67 vocab=b3faef47
-/
theorem two_mul_lt_sum_divisors {n : ℕ} (hn : n ≥ 6) :
    2 * n < ∑ k ∈ Icc 1 n, #k.divisors := by
  ---- By induction, we just have to check at `n = 6`.
  induction n, hn using Nat.le_induction with | base => decide | succ n hn n_ih => ?_
  replace hn : 1 < n + 1 := Nat.succ_lt_succ (Nat.zero_lt_of_lt hn)
  calc 2 * n + 2
    _ < ∑ k ∈ Icc 1 n, #k.divisors + #(n + 1).divisors :=
      Nat.add_lt_add_of_lt_of_le n_ih (one_lt_card_divisors hn)
    _ = ∑ k ∈ Icc 1 (n + 1), #k.divisors := (sum_Icc_succ_top hn.le _).symm

/-- If `p > 6` is prime, then `f(p) < f(p - 1)`.
@isnad1 id=lt.2h1v.s5.55d0163f93c7 from=translated src=- shape=a4fd0fe8 vocab=b79ce986
-/
theorem f_lt_pred_of_prime {p : ℕ} (hp : p > 6) (hp0 : p.Prime) : f p < f (p - 1) := by
  refine f_lt_f_of_sum_div ?_
  have hp1 : p - 1 + 1 = p := Nat.succ_pred_prime hp0
  calc (p - 1) * ∑ k ∈ Icc 1 p, #k.divisors
    _ = (p - 1) * ∑ k ∈ Icc 1 (p - 1 + 1), #k.divisors := by rw [hp1]
    _ = (p - 1) * ∑ k ∈ Icc 1 (p - 1), #k.divisors + 2 * (p - 1) := by
      rw [sum_Icc_succ_top (Nat.le_add_left _ _), hp1, hp0.divisors,
        card_pair hp0.ne_one.symm, Nat.mul_add, Nat.mul_comm _ 2]
    _ < (p - 1) * ∑ k ∈ Icc 1 (p - 1), #k.divisors + ∑ k ∈ Icc 1 (p - 1), #k.divisors :=
      Nat.add_lt_add_left (two_mul_lt_sum_divisors (Nat.le_pred_of_lt hp)) _
    _ = p * ∑ k ∈ Icc 1 (p - 1), #k.divisors := by rw [← Nat.add_one_mul, hp1]

/-- Final solution, part 2
@isnad1 id=ex.0h1v.s4.83c4abc98fb5 from=translated src=- shape=d6717ebf vocab=4d705f65
-/
theorem final_solution_part2 (N : ℕ) : ∃ n ≥ N, f (n + 1) < f n := by
  ---- Take any prime `p > max(6, N)`.
  obtain ⟨p, hp, hp0⟩ : ∃ p > max 6 N, Nat.Prime p := Nat.exists_infinite_primes _
  replace hp : p > 6 ∧ p > N := Nat.max_lt.mp hp
  ---- Then `n = p - 1` works.
  refine ⟨p - 1, Nat.le_pred_of_lt hp.2, ?_⟩
  calc f (p - 1 + 1)
    _ = f p := congrArg f (Nat.sub_add_cancel hp0.pos)
    _ < f (p - 1) := f_lt_pred_of_prime hp.1 hp0
