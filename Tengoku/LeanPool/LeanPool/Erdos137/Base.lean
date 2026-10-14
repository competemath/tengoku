/-
Copyright (c) 2026 Scott D. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott D. Hughes
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos137.Finiteness
public import Tengoku

/-!
# Erdős Problem #137: shared `g`-independent base layer

This file collects the low-level, **`g`-independent** helpers shared by every block route
(`JointFiniteness` `g = 3`, `SpliceFiniteness` `g = 5`, and the parametric `BlockFramework`).
It sits directly above `Finiteness` and below `BlockFramework`, so the generic framework and the
concrete `g = 3, 5` instances all derive from one base.

Two groups of helpers live here:

* **Block-tiling / radical algebra** (from the old `JointFiniteness`): the multiplicativity of `F`
  (`F_add`, `F_dvd_F_add`), the radical's prime support and factorization (`rad_dvd_self`,
  `primeFactors_rad`, `factorization_rad`, `rad_dvd_rad_of_dvd`), the elementary size bounds
  `le_F`, `le_F'`, `pow_le_F`, the interval-divisor counts (`Ioc_dvd_count`, `Ioc_dvd_le`), and the
  Legendre `i = 1` term `div_le_factorization_factorial`.
* **The smooth/rough split** (from the old `SmoothRefinement`): the primorial-type quantities
  `P`, `L`, the split `Ssmooth`/`Rrough`, and the smooth refinement
  `rad (F k n) ^ 2 * L k ≤ F k n * P k ^ 2` (`smooth_refinement`).

None of these mentions any block length `g` (or the concrete `B`/`W`/`overlap` of a route), so they
are proved once here and reused verbatim downstream.
-/

@[expose] public section

namespace Erdos137

open scoped BigOperators
open Finset

noncomputable section

/-! ## Basic facts about `F` and block tilings -/

/-- `F` splits as a product of an initial block and a shifted tail:
`F (a + b) n = F a n * F b (n + a)`.
@isnad1 id=eq.0h3v.s5.a5ec3508f796 from=translated src=- shape=bac28b96 vocab=f9dd656f
-/
lemma F_add (a b n : ℕ) : F (a + b) n = F a n * F b (n + a) := by
  unfold F
  rw [Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  ring_nf

/-- `F a n` divides `F (a + b) n`.
@isnad1 id=dvd.0h3v.s4.eeb503a213a8 from=translated src=- shape=01132874 vocab=4b351e38
-/
lemma F_dvd_F_add (a b n : ℕ) : F a n ∣ F (a + b) n := by
  rw [F_add]; exact Dvd.intro _ rfl

/-! ## The radical's prime support and factorization (general facts) -/

/-- `rad m ∣ m` for `m ≠ 0`.
@isnad1 id=dvd.1h1v.s4.21a333b71497 from=translated src=- shape=fc845374 vocab=ac0b3687
-/
lemma rad_dvd_self {m : ℕ} (_hm : m ≠ 0) : rad m ∣ m := by
  unfold rad; rw [Nat.support_factorization]; exact Nat.prod_primeFactors_dvd _

/-- The prime support of `rad m` is exactly `m.primeFactors` (for `m ≠ 0`).
@isnad1 id=eq.1h1v.s4.7800edc91e86 from=translated src=- shape=9acb563c vocab=62f3ae35
-/
lemma primeFactors_rad {m : ℕ} (hm : m ≠ 0) : (rad m).primeFactors = m.primeFactors := by
  apply Finset.Subset.antisymm
  · exact Nat.primeFactors_mono (rad_dvd_self hm) hm
  · intro p hp
    have hpprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hpdvd : p ∣ m := Nat.dvd_of_mem_primeFactors hp
    -- p ∈ support of rad m since p ∈ m.primeFactors = support of the product
    have : p ∣ rad m := by
      unfold rad; rw [Nat.support_factorization]
      exact Finset.dvd_prod_of_mem _ hp
    exact Nat.mem_primeFactors.mpr ⟨hpprime, this, Nat.one_le_iff_ne_zero.mp (rad_pos m)⟩

/-- **General fact:** `rad m` is squarefree, so `(rad m).factorization p = 1` if
`p ∈ m.primeFactors`, else `0`.
@isnad1 id=eq.1h2v.s6.222cf267b310 from=translated src=- shape=e2fd72bf vocab=20079f59
-/
lemma factorization_rad {m : ℕ} (hm : m ≠ 0) (p : ℕ) :
    (rad m).factorization p = if p ∈ m.primeFactors then 1 else 0 := by
  by_cases hp : p ∈ m.primeFactors
  · simp only [hp, ite_true]
    have hpprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
    unfold rad
    rw [Nat.support_factorization]
    rw [Nat.factorization_prod_apply (by
      intro q hq; exact (Nat.prime_of_mem_primeFactors hq).ne_zero)]
    rw [Finset.sum_eq_single p]
    · exact Nat.Prime.factorization_self hpprime
    · simp_all
    · intro h; exact absurd hp h
  · simp only [hp, ite_false]
    by_cases hpp : p.Prime
    · rw [Nat.factorization_eq_zero_of_not_dvd]
      intro hdvd
      apply hp
      exact Nat.mem_primeFactors.mpr
        ⟨hpp, dvd_trans hdvd (rad_dvd_self hm), hm⟩
    · exact Nat.factorization_eq_zero_of_not_prime _ hpp

/-- `rad` is monotone under divisibility: `a ∣ b`, `b ≠ 0` ⟹ `rad a ∣ rad b`
(their prime supports are nested).
@isnad1 id=dvd.2h2v.s4.860348f7b0cc from=translated src=- shape=fc60dc7a vocab=ac0b3687
-/
lemma rad_dvd_rad_of_dvd {a b : ℕ} (hb : b ≠ 0) (hab : a ∣ b) : rad a ∣ rad b := by
  unfold rad
  rw [Nat.support_factorization, Nat.support_factorization]
  apply Finset.prod_dvd_prod_of_subset
  exact Nat.primeFactors_mono hab hb

/-! ## Elementary size bounds on `F k n` -/

/-- `n ≤ F k n` for `k ≥ 1`, `n ≥ 1` (the first factor is `n`, the rest are `≥ 1`).
@isnad1 id=le.2h2v.s4.7b7c7b25d034 from=translated src=- shape=54f6f2a6 vocab=0ae0e3a6
-/
lemma le_F {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) : n ≤ F k n := by
  have hmem : (0 : ℕ) ∈ Finset.range k := Finset.mem_range.mpr (by omega)
  have hdvd : (n + 0) ∣ F k n := by
    rw [F]; exact Finset.dvd_prod_of_mem _ hmem
  simpa using Nat.le_of_dvd (F_pos hn) hdvd

/-- `k ≤ F k n` for `k ≥ 1`, `n ≥ 1` (the last factor `n+k-1 ≥ k` divides the product).
@isnad1 id=le.2h2v.s4.a2c4844b9c25 from=translated src=- shape=fd8db9e9 vocab=0ae0e3a6
-/
lemma le_F' {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) : k ≤ F k n := by
  have hmem : (k - 1) ∈ Finset.range k := Finset.mem_range.mpr (by omega)
  have hdvd : (n + (k - 1)) ∣ F k n := by
    rw [F]; exact Finset.dvd_prod_of_mem _ hmem
  have : k ≤ n + (k - 1) := by omega
  exact le_trans this (Nat.le_of_dvd (F_pos hn) hdvd)

/-! ## Counting multiples of a prime in an interval (for the overlap bound) -/

/-- **Exact count** of multiples of `p` in `(a, b]`: `#{x ∈ Ioc a b | p ∣ x} = b/p − a/p`.
@isnad1 id=eq.1h3v.s5.19c9f3dcdebb from=translated src=- shape=14983e83 vocab=878cca52
-/
theorem Ioc_dvd_count (a b p : ℕ) (hab : a ≤ b) :
    #{x ∈ Finset.Ioc a b | p ∣ x} = b / p - a / p := by
  have h1 : #{x ∈ Finset.Ioc 0 b | p ∣ x} = b / p := Nat.Ioc_filter_dvd_card_eq_div b p
  have h2 : #{x ∈ Finset.Ioc 0 a | p ∣ x} = a / p := Nat.Ioc_filter_dvd_card_eq_div a p
  have hsplit : #{x ∈ Finset.Ioc 0 b | p ∣ x}
      = #{x ∈ Finset.Ioc 0 a | p ∣ x} + #{x ∈ Finset.Ioc a b | p ∣ x} := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      rw [← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le a) hab]
    · apply Finset.disjoint_filter_filter
      rw [Finset.Ioc_disjoint_Ioc]; simp
  omega

/-- The number of multiples of `p` in an interval of length `L` is at most `⌊L/p⌋ + 1`.
@isnad1 id=le.1h3v.s6.d2fcc2e72048 from=translated src=- shape=e2f720ea vocab=09e98e38
-/
theorem Ioc_dvd_le (a L p : ℕ) (hp : 1 ≤ p) :
    #{x ∈ Finset.Ioc a (a + L) | p ∣ x} ≤ L / p + 1 := by
  rw [Ioc_dvd_count a (a + L) p (Nat.le_add_right a L)]
  have hpp : 0 < p := hp
  have h6 : (a + L) / p = (a / p + L / p) + (a % p + L % p) / p := by
    have h5 : (a + L) = p * (a / p + L / p) + (a % p + L % p) := by
      have hma : p * (a / p + L / p) = p * (a / p) + p * (L / p) := by ring
      have h1 : p * (a / p) + a % p = a := Nat.div_add_mod a p
      have h2 : p * (L / p) + L % p = L := Nat.div_add_mod L p
      rw [hma]; omega
    rw [h5, Nat.mul_add_div hpp]
  have h7 : (a % p + L % p) / p ≤ 1 := by
    have h3 : a % p < p := Nat.mod_lt _ hpp
    have h4 : L % p < p := Nat.mod_lt _ hpp
    rw [Nat.div_le_iff_le_mul_add_pred hpp]; omega
  rw [Nat.sub_le_iff_le_add, h6]; omega

/-- For a prime `p`, `⌊k/p⌋ ≤ (k!).factorization p` (the `i = 1` term of Legendre's formula).
@isnad1 id=le.1h2v.s5.d72b15e16fcc from=translated src=- shape=0c730828 vocab=e92ee4b2
-/
lemma div_le_factorization_factorial {k p : ℕ} (hp : p.Prime) :
    k / p ≤ (Nat.factorial k).factorization p := by
  rw [Nat.factorization_factorial hp (Nat.lt_add_one (Nat.log p k))]
  by_cases hpk : 1 ≤ Nat.log p k
  · have hmem : 1 ∈ Finset.Ico 1 (Nat.log p k + 1) := by
      simp only [Finset.mem_Ico]; omega
    calc k / p = k / p ^ 1 := by rw [pow_one]
      _ ≤ ∑ i ∈ Finset.Ico 1 (Nat.log p k + 1), k / p ^ i :=
          Finset.single_le_sum (f := fun i => k / p ^ i) (by intro i _; positivity) hmem
  · have hlt : k < p := by
      by_contra hc; push Not at hc
      exact absurd (Nat.log_pos hp.one_lt hc) (by omega)
    rw [Nat.div_eq_of_lt hlt]; exact Nat.zero_le _

/-! ## The primorial-type quantities `P k` and `L k` -/

/-- `P k = ∏_{p ∈ primesBelow k} p` — the product of the primes `< k` (the primorial of `k`). -/
def P (k : ℕ) : ℕ := ∏ p ∈ Nat.primesBelow k, p

/-- `L k = ∏_{p ∈ primesBelow k} p ^ (k / p)` — the smooth-part lower bound (`L ∣ k!` by Legendre,
`L = (k!)^{1-o(1)}`). -/
def L (k : ℕ) : ℕ := ∏ p ∈ Nat.primesBelow k, p ^ (k / p)

/--
@isnad1 id=le.0h1v.s3.3ec638a3a47a from=translated src=- shape=8a62b088 vocab=96d977a5
-/
lemma P_pos (k : ℕ) : 1 ≤ P k :=
  Finset.one_le_prod fun _p hp => (Nat.prime_of_mem_primesBelow hp).one_le

/--
@isnad1 id=le.0h1v.s3.1ea3bdfc660c from=translated src=- shape=8a62b088 vocab=9f32d364
-/
lemma L_pos (k : ℕ) : 1 ≤ L k :=
  Finset.one_le_prod fun _p hp => Nat.one_le_pow _ _ (Nat.prime_of_mem_primesBelow hp).pos

/--
@isnad1 id=ne.0h1v.s3.bda9b7c50145 from=translated src=- shape=b14ee516 vocab=bb7e4ca9
-/
lemma L_ne_zero (k : ℕ) : L k ≠ 0 := Nat.one_le_iff_ne_zero.mp (L_pos k)

/-- `P k ≤ 4 ^ k` (Mathlib's `primorial_le_four_pow`; `primesBelow k` are the primes `≤ k - 1`,
a subset of the primes counted by `primorial k`).
@isnad1 id=le.0h1v.s4.ed7270e30f14 from=translated src=- shape=ff508864 vocab=7d0a8f26
-/
lemma P_le_4_pow (k : ℕ) : P k ≤ 4 ^ k := by
  have hsub : Nat.primesBelow k ⊆ {p ∈ Finset.range (k + 1) | p.Prime} := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hp.2⟩
  have hdvd : P k ∣ primorial k := by
    unfold P primorial
    exact Finset.prod_dvd_prod_of_subset _ _ _ hsub
  calc P k ≤ primorial k := Nat.le_of_dvd (primorial_pos k) hdvd
    _ ≤ 4 ^ k := primorial_le_four_pow k

/-! ## The smooth/rough split of `F k n` -/

/-- The smooth part `S k n = ∏_{p | F, p < k} p ^ v_p(F)`. -/
def Ssmooth (k n : ℕ) : ℕ :=
  ∏ p ∈ (F k n).primeFactors.filter (· < k), p ^ (F k n).factorization p

/-- The rough part `R k n = ∏_{p | F, ¬ p < k} p ^ v_p(F)`. -/
def Rrough (k n : ℕ) : ℕ :=
  ∏ p ∈ (F k n).primeFactors.filter (fun p => ¬ p < k), p ^ (F k n).factorization p

/-- `S · R = F` for `n ≥ 1`.
@isnad1 id=eq.1h2v.s5.4e8d2d519548 from=translated src=- shape=c4f6e16b vocab=a0adb648
-/
lemma Ssmooth_mul_Rrough {k n : ℕ} (hn : 1 ≤ n) : Ssmooth k n * Rrough k n = F k n := by
  unfold Ssmooth Rrough
  rw [Finset.prod_filter_mul_prod_filter_not]
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self (F_ne_zero hn)]
  rw [Nat.prod_factorization_eq_prod_primeFactors]

/--
@isnad1 id=le.1h2v.s4.1b73af1c019b from=translated src=- shape=61bdc3e7 vocab=50bd04a2
-/
lemma Ssmooth_pos {k n : ℕ} (_hn : 1 ≤ n) : 1 ≤ Ssmooth k n :=
  Finset.one_le_prod fun _p hp =>
    Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter _ hp)).pos

/--
@isnad1 id=le.1h2v.s4.5da4a564e852 from=translated src=- shape=61bdc3e7 vocab=aaee85ac
-/
lemma Rrough_pos {k n : ℕ} (_hn : 1 ≤ n) : 1 ≤ Rrough k n :=
  Finset.one_le_prod fun _p hp =>
    Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter _ hp)).pos

/-! ## Bound on the smooth radical: `rad(S)^2 ≤ P^2` -/

/-- `∏_{p | F, p < k} p ∣ P k`: the smooth prime factors are a subset of `primesBelow k`.
@isnad1 id=dvd.0h2v.s5.46eb2d7ce0b9 from=translated src=- shape=cb33941d vocab=35028fe6
-/
lemma smooth_rad_dvd_P {k n : ℕ} :
    (∏ p ∈ (F k n).primeFactors.filter (· < k), p) ∣ P k := by
  unfold P
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  rw [Finset.mem_filter] at hp
  rw [Nat.mem_primesBelow]
  exact ⟨hp.2, Nat.prime_of_mem_primeFactors hp.1⟩

/-- `∏_{p | F, p < k} p ≤ P k`.
@isnad1 id=le.0h2v.s5.a4f3beecf1e8 from=translated src=- shape=cb33941d vocab=b43febdd
-/
lemma smooth_rad_le_P {k n : ℕ} :
    (∏ p ∈ (F k n).primeFactors.filter (· < k), p) ≤ P k :=
  Nat.le_of_dvd (P_pos k) smooth_rad_dvd_P

/-! ## Bound on the rough part: `∏_{p | F, ¬ p<k} p^2 ≤ R` (powerful) -/

/-! ## The smooth lower bound: `L ∣ S` and `L ≤ S`

We need `v_p(F) ≥ ⌊k/p⌋` for every prime `p < k`. Among the `k` consecutive integers
`n, …, n+k-1` (the multiset `(n-1, n-1+k]` shifted), at least `⌊k/p⌋` are divisible by `p`, and
each such factor contributes at least `1` to `v_p(F)`. -/

/-- The count of multiples of `p` among the `k` consecutive integers `n, …, n+k-1` is at least
`⌊k/p⌋`. Stated via the exact `Ioc` count:
`#{x ∈ (n-1, n-1+k] | p ∣ x} = (n-1+k)/p − (n-1)/p ≥ k/p`.
@isnad1 id=le.2h3v.s5.217c65a3abfe from=translated src=- shape=d28a7ce2 vocab=154340b2
-/
lemma div_le_factorization_F {k n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime) :
    k / p ≤ (F k n).factorization p := by
  -- v_p(F) = ∑_{i<k} v_p(n+i) ≥ #{i<k | p ∣ n+i} = #{x ∈ (n-1, n-1+k] | p∣x} ≥ k/p.
  set D : Finset ℕ := (Finset.range k).filter (fun i => p ∣ (n + i)) with hD
  -- Lower bound: each multiple contributes ≥ 1.
  have hfac : (F k n).factorization p = ∑ i ∈ Finset.range k, (n + i).factorization p := by
    unfold F
    rw [Nat.factorization_prod (by intro i _; omega)]
    rw [Finset.sum_apply']
  have hcount_le : #D ≤ (F k n).factorization p := by
    rw [hfac]
    calc #D = ∑ i ∈ D, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ i ∈ D, (n + i).factorization p := by
          apply Finset.sum_le_sum
          intro i hi
          rw [hD, Finset.mem_filter] at hi
          have hne : n + i ≠ 0 := by omega
          exact (Nat.Prime.pow_dvd_iff_le_factorization hp hne).mp (by simpa using hi.2)
      _ ≤ ∑ i ∈ Finset.range k, (n + i).factorization p :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (by intro i _ _; positivity)
  -- Relate #D to the Ioc count of multiples.
  have hbij : #D = #{x ∈ Finset.Ioc (n - 1) (n - 1 + k) | p ∣ x} := by
    apply Finset.card_bij (fun i _ => n + i)
    · intro i hi
      rw [hD, Finset.mem_filter, Finset.mem_range] at hi
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨by omega, by omega⟩, hi.2⟩
    · intro i hi j hj h; omega
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hx
      obtain ⟨⟨hx1, hx2⟩, hxdvd⟩ := hx
      refine ⟨x - n, ?_, ?_⟩
      · rw [hD, Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_⟩
        rw [show n + (x - n) = x by omega]; exact hxdvd
      · omega
  have hcount : #{x ∈ Finset.Ioc (n - 1) (n - 1 + k) | p ∣ x} = (n - 1 + k) / p - (n - 1) / p :=
    Ioc_dvd_count (n - 1) (n - 1 + k) p (by omega)
  -- ⌊(a+k)/p⌋ − ⌊a/p⌋ ≥ ⌊k/p⌋.
  have hkey : k / p ≤ (n - 1 + k) / p - (n - 1) / p := by
    have h1 : (n - 1) / p + k / p ≤ (n - 1 + k) / p := Nat.div_add_div_le_add_div
    omega
  omega

/-- `L k ∣ F k n` for `n ≥ 1`: `v_p(L) = ⌊k/p⌋ ≤ v_p(F)` for every prime `p < k`.
@isnad1 id=dvd.1h2v.s4.2815c4cea56c from=translated src=- shape=b9937f24 vocab=3f5aee8a
-/
lemma L_dvd_F {k n : ℕ} (hn : 1 ≤ n) : L k ∣ F k n := by
  rw [← Nat.factorization_le_iff_dvd (L_ne_zero k) (F_ne_zero hn)]
  intro p
  rw [show L k = ∏ q ∈ Nat.primesBelow k, q ^ (k / q) from rfl]
  rw [Nat.factorization_prod (fun q hq => by
    simp_all)]
  rw [Finset.sum_apply']
  by_cases hp : p ∈ Nat.primesBelow k
  · have hpp : p.Prime := Nat.prime_of_mem_primesBelow hp
    have hsingle : (∑ q ∈ Nat.primesBelow k, (q ^ (k / q)).factorization p)
        = (p ^ (k / p)).factorization p :=
      Finset.sum_eq_single p
        (fun q hq hqp => by
          have hqp' : q.Prime := Nat.prime_of_mem_primesBelow hq
          rw [Nat.Prime.factorization_pow hqp', Finsupp.single_apply, ite_eq_right hqp])
        (fun h => absurd hp h)
    rw [hsingle, Nat.Prime.factorization_pow hpp, Finsupp.single_apply, ite_eq_left rfl]
    exact div_le_factorization_F hn hpp
  · have hzero : (∑ q ∈ Nat.primesBelow k, (q ^ (k / q)).factorization p) = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      have hqp' : q.Prime := Nat.prime_of_mem_primesBelow hq
      have hne : q ≠ p := by rintro rfl; exact hp hq
      rw [Nat.Prime.factorization_pow hqp', Finsupp.single_apply, ite_eq_right hne]
    rw [hzero]; exact Nat.zero_le _

/-- `L k ≤ S k n` (the smooth part): `L ∣ F` and `L`'s primes are exactly the smooth primes, so in
fact `L ∣ S`; we only need `L ≤ S`.
@isnad1 id=dvd.1h2v.s4.294c17fd64f2 from=translated src=- shape=b9937f24 vocab=767a2017
-/
lemma L_le_smooth {k n : ℕ} (hn : 1 ≤ n) : L k ∣ Ssmooth k n := by
  -- L ∣ F and all prime factors of L are < k, so L ∣ S (the < k part of F).
  rw [← Nat.factorization_le_iff_dvd (L_ne_zero k) (Nat.one_le_iff_ne_zero.mp (Ssmooth_pos hn))]
  intro p
  have hLdvdF : L k ∣ F k n := L_dvd_F hn
  by_cases hp : p ∈ Nat.primesBelow k
  · have hpp : p.Prime := Nat.prime_of_mem_primesBelow hp
    have hplt : p < k := Nat.lt_of_mem_primesBelow hp
    -- v_p(L) ≤ v_p(F) = v_p(S) since p < k.
    have hvLF : (L k).factorization p ≤ (F k n).factorization p :=
      (Nat.factorization_le_iff_dvd (L_ne_zero k) (F_ne_zero hn)).mpr hLdvdF p
    have hvFS : (F k n).factorization p ≤ (Ssmooth k n).factorization p := by
      by_cases hpdvd : p ∈ (F k n).primeFactors
      · unfold Ssmooth
        rw [Nat.factorization_prod (fun q hq => by
          have := (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter _ hq)).pos; positivity)]
        rw [Finset.sum_apply']
        have hmem : p ∈ (F k n).primeFactors.filter (· < k) := by
          rw [Finset.mem_filter]; exact ⟨hpdvd, hplt⟩
        rw [Finset.sum_eq_single p
              (fun q hq hqp => by
                simp_all)
              (fun h => absurd hmem h)]
        rw [Nat.Prime.factorization_pow hpp, Finsupp.single_apply, ite_eq_left rfl]
      · -- p ∤ F ⇒ v_p(F) = 0
        rw [Nat.factorization_eq_zero_of_not_dvd]
        · exact Nat.zero_le _
        · intro hdvd; exact hpdvd (Nat.mem_primeFactors.mpr ⟨hpp, hdvd, F_ne_zero hn⟩)
    exact le_trans hvLF hvFS
  · have hzero : (L k).factorization p = 0 := by
      rw [show L k = ∏ q ∈ Nat.primesBelow k, q ^ (k / q) from rfl]
      rw [Nat.factorization_prod (fun q hq => by
        have := (Nat.prime_of_mem_primesBelow hq).pos; positivity)]
      rw [Finset.sum_apply']
      apply Finset.sum_eq_zero
      intro q hq
      have hqp' : q.Prime := Nat.prime_of_mem_primesBelow hq
      have hne : q ≠ p := by rintro rfl; exact hp hq
      rw [Nat.Prime.factorization_pow hqp', Finsupp.single_apply, ite_eq_right hne]
    rw [hzero]; exact Nat.zero_le _

/-! ## `rad (F k n)` factored through the smooth/rough split -/

/-- `rad (F k n) = (∏_{p|F, p<k} p) · (∏_{p|F, ¬p<k} p)`.
@isnad1 id=eq.0h2v.s6.8a05154991ef from=translated src=- shape=526ea6cc vocab=63da6137
-/
lemma rad_smooth_rough_split (k n : ℕ) :
    rad (F k n)
      = (∏ p ∈ (F k n).primeFactors.filter (· < k), p)
        * (∏ p ∈ (F k n).primeFactors.filter (fun p => ¬ p < k), p) := by
  unfold rad
  rw [Nat.support_factorization]
  rw [Finset.prod_filter_mul_prod_filter_not]

/-! ## The smooth refinement -/

end  -- noncomputable section

end Erdos137
