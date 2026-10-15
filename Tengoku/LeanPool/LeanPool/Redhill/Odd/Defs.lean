/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Tengoku.LeanPool.LeanPool.Redhill.Common.PairwiseCoprime
public import Tengoku.LeanPool.LeanPool.Redhill.Common.VWPair
public import Tengoku

/-!
# Definitions for the odd case

The lower bound `s` for `primeChain` in `U` was originally `max 16 (F.sup id)`.
This could be lowered because `strongSSC_vwTup` only requires `m ≤ s`, not `2m ≤ s`.
-/

@[expose] public section

namespace OddCase

open Nat Fin Finset

variable (n : ℕ) (F : Finset ℕ)

/-- The sum of `tup` over all indices save `n` and `n + 1`, i.e. the input `u` to `VWPair`. -/
def U : ℕ := 8 + ∑ i ∈ range n, primeChain (max 8 (F.sup id)) i

/-- The `VWPair` generated from the inputs `u = U n F, m = max (U n F) (F.sup id)`. -/
def VW : VWPair (U n F) (max (U n F) (F.sup id)) := .of ..

/-- We require `x` in `tup` to be a multiple of this number,
an optimised version of the paper's `y`. -/
def Y : ℕ :=
  10 * (F.erase 0).prod id *
  (∏ i ∈ range n, primeChain (max 8 (F.sup id)) i) * (VW n F).v * (VW n F).w

/-- The sequence of `(n + 5)`-tuples containing an infinite subsequence in `factorFreeTuples`
whose qualities tend to `5 / 3`, assuming `n` is even and `0, 1, 2, 5, 10 ∉ F`. -/
def tup (x : ℤ) (i : Fin (n + 5)) : ℤ :=
  i.addCases (primeChain (max 8 (F.sup id)) ·.1) fun
    | 0 => (VW n F).v
    | 1 => -(VW n F).w
    | 2 => (x - 1) ^ 5
    | 3 => 10 * (x ^ 2 + 1) ^ 2
    | 4 => -(x + 1) ^ 5

variable {n F} {x : ℤ}

-- Not `@[simp]`: with `Fin.castAdd_to_castSucc` from another pool project in the global
-- simp set, the left-hand side `i.castAdd 5` is rewritten to a `Fin.castSucc` chain, so this
-- lemma's left-hand side is no longer in simp normal form. All call sites invoke it explicitly.
/--
@isnad1 id=eq.0h4v.s5.79769834ebb9 from=translated src=- shape=f7facd6f vocab=36fbdfe5
-/
lemma tup_castAdd {i : Fin n} :
    tup n F x (i.castAdd 5) = primeChain (max 8 (F.sup id)) i.1 := by
  simp [tup]

/--
@isnad1 id=eq.0h3v.s5.113f0f9c8d9d from=translated src=- shape=efb47a3c vocab=c3ad4e29
-/
@[simp] lemma tup_natAdd_zero : tup n F x (natAdd n 0) = (VW n F).v := by simp [tup]

/--
@isnad1 id=eq.0h3v.s6.8cffe4b43cec from=translated src=- shape=7adde2fe vocab=c7d7d39a
-/
@[simp] lemma tup_natAdd_one : tup n F x (natAdd n 1) = -(VW n F).w := by simp [tup]

/--
@isnad1 id=eq.0h3v.s6.03513c0bec44 from=translated src=- shape=b0afcf65 vocab=42c2f3f7
-/
@[simp] lemma tup_natAdd_two : tup n F x (natAdd n 2) = (x - 1) ^ 5 := by simp [tup]

/--
@isnad1 id=eq.0h3v.s6.f7fe7691366d from=translated src=- shape=af33e0eb vocab=69de2b31
-/
@[simp] lemma tup_natAdd_three : tup n F x (natAdd n 3) = 10 * (x ^ 2 + 1) ^ 2 := by simp [tup]

/--
@isnad1 id=eq.0h3v.s6.4edcd51631f4 from=translated src=- shape=b9c7f77b vocab=54cd4013
-/
@[simp] lemma tup_natAdd_four : tup n F x (natAdd n 4) = -(x + 1) ^ 5 := by simp [tup]

/--
@isnad1 id=eq.0h3v.s6.146f9127a250 from=translated src=- shape=f8803b88 vocab=c8a379d1
-/
lemma sum_tup : ∑ i, tup n F x i = 0 := by
  simp only [tup, sum_univ_add, addCases_left, addCases_right, sum_univ_five,
    add_assoc, show (x - 1) ^ 5 + (10 * (x ^ 2 + 1) ^ 2 + -(x + 1) ^ 5) = 8 by ring]
  rw [(VW n F).eq_add, cast_add, neg_add, ← add_assoc _ _ 8, add_add_neg_cancel'_right,
    sum_univ_eq_sum_range fun i ↦ (primeChain _ i : ℤ)]
  norm_num [U]

variable {i : Fin n}

section Bounds

/--
@isnad1 id=lt.0h3v.s5.c8c950bdce24 from=translated src=- shape=b640da36 vocab=64d99402
-/
lemma primeChain_lt_U : primeChain (max 8 (F.sup id)) i.1 < U n F :=
  (single_le_sum_of_canonicallyOrdered (by simp_all)).trans_lt (lt_add_of_pos_left _ (by decide))

/--
@isnad1 id=lt.0h2v.s5.b9826d4c936c from=translated src=- shape=fd88d611 vocab=73e6664f
-/
lemma ten_lt_primeChain : 10 < primeChain (max 8 (F.sup id)) n := by
  grind [primeChain_gt, prime_primeChain, show ¬Nat.Prime 9 ∧ ¬Nat.Prime 10 by decide]

/--
@isnad1 id=mem.0h3v.s6.474ee74afa4e from=translated src=- shape=cd184732 vocab=312c42f9
-/
lemma primeChain_mem_Icc : primeChain (max 8 (F.sup id)) i.1 ∈ Icc 3 (max (U n F) (F.sup id)) :=
  mem_Icc.mpr ⟨ten_lt_primeChain.trans' (by decide), le_max_iff.mpr (.inl primeChain_lt_U.le)⟩

/--
@isnad1 id=lt.0h2v.s5.49dc59dd0b32 from=translated src=- shape=a2e8936a vocab=cd3e1816
-/
lemma U_lt_V : U n F < (VW n F).v :=
  calc
    _ ≤ max (U n F) (F.sup id) := le_max_left ..
    _ < _ := (VW n F).m_lt_v

/--
@isnad1 id=lt.0h2v.s5.c841bc8a1fc4 from=translated src=- shape=a2e8936a vocab=a9e8cab4
-/
lemma U_lt_W : U n F < (VW n F).w := by grind [U_lt_V, (VW n F).eq_add]

/--
@isnad1 id=le.0h2v.s5.07b3d1bf81fa from=translated src=- shape=01efd551 vocab=37ca04b7
-/
lemma V_lower_bound : 9 ≤ (VW n F).v :=
  calc
    _ ≤ max (U n F) (F.sup id) := by grind [U]
    _ < _ := (VW n F).m_lt_v

/--
@isnad1 id=le.0h2v.s5.7e9243bcf5f6 from=translated src=- shape=01efd551 vocab=c7dd2dd0
-/
lemma W_lower_bound : 17 ≤ (VW n F).w := by grind [U, (VW n F).eq_add, V_lower_bound]

/--
@isnad1 id=le.0h2v.s4.89eacdbc0ac1 from=translated src=- shape=f8de4f81 vocab=5aa41376
-/
lemma Y_lower_bound : 1530 ≤ Y n F := by
  rw [show 1530 = 10 * 1 * 1 * 9 * 17 by rfl, Y]
  gcongr
  · exact one_le_prod (by grind)
  · exact one_le_prod (by grind [ten_lt_primeChain])
  · exact V_lower_bound
  · exact W_lower_bound

/--
@isnad1 id=lt.0h2v.s4.e04f6be805c0 from=translated src=- shape=f8de4f81 vocab=1885a6a6
-/
lemma Y_pos : 0 < Y n F := by grind [Y_lower_bound]

end Bounds

section Coprime

/--
@isnad1 id=and.1h3v.s7.2f1fc385d1b7 from=translated src=- shape=c465ec3a vocab=6dd73650
-/
lemma dvd_of_Y_dvd (dx : ↑(Y n F) ∣ x) :
    10 ∣ x ∧ (∀ f ∈ F.erase 0, ↑f ∣ x) ∧ (∀ i : Fin n, ↑(primeChain (max 8 (F.sup id)) i.1) ∣ x) ∧
    ↑(VW n F).v ∣ x ∧ ↑(VW n F).w ∣ x := by
  simp_rw [Y, cast_mul, cast_ofNat, cast_prod, id_eq] at dx
  simp_rw [← and_assoc]
  iterate 2
    refine ⟨?_, dvd_of_mul_left_dvd dx⟩
    replace dx := dvd_of_mul_right_dvd dx
  refine ⟨?_, fun i ↦ ?_⟩
  · replace dx := dvd_of_mul_right_dvd dx
    exact ⟨dvd_of_mul_right_dvd dx,
      fun f mf ↦ (dvd_prod_of_mem _ mf).trans (dvd_of_mul_left_dvd dx)⟩
  · refine dvd_trans ?_ (dvd_of_mul_left_dvd dx)
    rw [← Fin.prod_univ_eq_prod_range]
    exact dvd_prod_of_mem _ (mem_univ _)

/--
@isnad1 id=iscoprim.1h5v.s5.9eebdcf96d1e from=translated src=- shape=434808e2 vocab=8083700f
-/
lemma isCoprime_tup_castAdd_natAdd {j : Fin 5} (dx : ↑(Y n F) ∣ x) :
    IsCoprime (tup n F x (castAdd 5 i)) (tup n F x (natAdd n j)) := by
  rw [tup_castAdd]
  replace dx := (dvd_of_Y_dvd dx).2.2.1
  fin_cases j <;> simp only [reduceFinMk]
  · rw [tup_natAdd_zero, isCoprime_iff_coprime, prime_primeChain.coprime_iff_not_dvd]
    exact ((VW n F).not_dvd _ primeChain_mem_Icc).1
  · rw [tup_natAdd_one, IsCoprime.neg_right_iff, isCoprime_iff_coprime,
      prime_primeChain.coprime_iff_not_dvd]
    exact ((VW n F).not_dvd _ primeChain_mem_Icc).2
  · rw [tup_natAdd_two, IsCoprime.pow_right_iff (by decide)]
    exact IsCoprime.sub_one_right_of_dvd (dx _)
  · rw [tup_natAdd_three, IsCoprime.mul_right_iff, IsCoprime.pow_right_iff zero_lt_two]
    constructor
    · norm_cast
      exact coprime_of_lt_prime (by decide) (by grind [ten_lt_primeChain]) prime_primeChain
    · exact IsCoprime.add_one_right_of_dvd (dvd_pow (dx i) two_ne_zero)
  · rw [tup_natAdd_four, IsCoprime.neg_right_iff, IsCoprime.pow_right_iff (by decide)]
    exact IsCoprime.add_one_right_of_dvd (dx _)

/-- This lemma is where we need evenness of `n`, i.e. oddness of the whole tuple's length.
@isnad1 id=coprime.1h2v.s5.693225660140 from=translated src=- shape=59ace710 vocab=ef18001c
-/
lemma V_coprime_ten (hn : Even n) : (VW n F).v.Coprime 10 := by
  rw [show 10 = 2 * 5 by rfl]
  apply Coprime.mul_right
  · rw [coprime_two_right]
    have key : Even (U n F) := by
      apply Even.add (by decide)
      simp_rw [even_sum_iff_even_card_odd, prime_primeChain.odd_iff]
      have (i : ℕ) : 3 ≤ primeChain (max 8 (F.sup id)) i :=
        ten_lt_primeChain.le.trans' (by decide)
      simpa [this]
    grind [(VW n F).w_odd, (VW n F).eq_add]
  · rw [coprime_comm, prime_five.coprime_iff_not_dvd]
    exact ((VW n F).not_dvd 5 (mem_Icc.mpr ⟨by decide, by grind [U]⟩)).1

/--
@isnad1 id=coprime.0h2v.s5.a052699ab774 from=translated src=- shape=6e586dd4 vocab=00060133
-/
lemma W_coprime_ten : (VW n F).w.Coprime 10 := by
  rw [show 10 = 2 * 5 by rfl]
  apply Coprime.mul_right
  · rw [coprime_two_right]
    exact (VW n F).w_odd
  · rw [coprime_comm, prime_five.coprime_iff_not_dvd]
    exact ((VW n F).not_dvd 5 (mem_Icc.mpr ⟨by decide, by grind [U]⟩)).2

/--
@isnad1 id=pairwise.2h3v.s5.cb90f3641da0 from=translated src=- shape=c00047ed vocab=9c93756d
-/
lemma pairwiseCoprime_tup (hn : Even n) (dx : ↑(Y n F) ∣ x) : PairwiseCoprime (tup n F x) := by
  have : Std.Symm (fun i j ↦ IsCoprime (tup n F x i) (tup n F x j)) :=
    ⟨fun {a b} (h : IsCoprime (tup n F x a) (tup n F x b)) ↦ h.symm⟩
  refine Pairwise.of_lt fun i j h ↦ ?_
  cases i using Fin.addCases <;> cases j using Fin.addCases
  case left.left i j =>
    simp only [tup_castAdd, isCoprime_iff_coprime]
    rw [coprime_primes prime_primeChain prime_primeChain]
    exact (strictMono_primeChain h).ne
  case left.right i j => exact isCoprime_tup_castAdd_natAdd dx
  case right.left i j => grind
  case right.right i j =>
    rw [natAdd_lt_natAdd_iff] at h
    obtain ⟨d10, -, -, dv, dw⟩ := dvd_of_Y_dvd dx
    have d2 : 2 ∣ x := dvd_trans (by decide) d10
    have cp2 := IsCoprime.add_one_sub_one_of_two_dvd (dvd_pow d2 two_ne_zero)
    rw [show x ^ 2 - 1 = (x + 1) * (x - 1) by ring, IsCoprime.mul_right_iff] at cp2
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by lia
    · rw [tup_natAdd_zero]
      obtain rfl | rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by lia
      · rw [tup_natAdd_one, IsCoprime.neg_right_iff, isCoprime_iff_coprime]
        exact VWPair.of_coprime (by grind [U]) (le_max_left ..)
      · rw [tup_natAdd_two]
        exact (IsCoprime.sub_one_right_of_dvd dv).pow_right
      · rw [tup_natAdd_three, IsCoprime.mul_right_iff]
        refine ⟨?_, (IsCoprime.add_one_right_of_dvd (dvd_pow dv two_ne_zero)).pow_right⟩
        exact_mod_cast V_coprime_ten hn
      · rw [tup_natAdd_four]
        exact (IsCoprime.add_one_right_of_dvd dv).pow_right.neg_right
    · rw [tup_natAdd_one, IsCoprime.neg_left_iff]
      obtain rfl | rfl | rfl : j = 2 ∨ j = 3 ∨ j = 4 := by lia
      · rw [tup_natAdd_two]
        exact (IsCoprime.sub_one_right_of_dvd dw).pow_right
      · rw [tup_natAdd_three, IsCoprime.mul_right_iff]
        refine ⟨?_, (IsCoprime.add_one_right_of_dvd (dvd_pow dw two_ne_zero)).pow_right⟩
        exact_mod_cast W_coprime_ten
      · rw [tup_natAdd_four]
        exact (IsCoprime.add_one_right_of_dvd dw).pow_right.neg_right
    · rw [tup_natAdd_two, IsCoprime.pow_left_iff (by decide)]
      obtain rfl | rfl : j = 3 ∨ j = 4 := by lia
      · rw [tup_natAdd_three, IsCoprime.mul_right_iff]
        exact ⟨IsCoprime.sub_one_left_of_dvd d10, (cp2.2.symm).pow_right⟩
      · rw [tup_natAdd_four]
        exact (IsCoprime.add_one_sub_one_of_two_dvd d2).symm.pow_right.neg_right
    · obtain rfl : j = 4 := by lia
      rw [tup_natAdd_three, tup_natAdd_four, IsCoprime.neg_right_iff,
        IsCoprime.pow_right_iff (by decide), IsCoprime.mul_left_iff]
      exact ⟨IsCoprime.add_one_right_of_dvd d10, cp2.1.pow_left⟩

/--
@isnad1 id=lt.1h3v.s5.0b52ba803c28 from=translated src=- shape=0656c490 vocab=ef5c2c62
-/
lemma lt_primeChain_of_mem_F {f : ℕ} (hf : f ∈ F) : f < primeChain (max 8 (F.sup id)) n :=
  calc
    _ ≤ F.sup id := le_sup hf
    _ < _ := by grind [primeChain_gt]

/--
@isnad1 id=not.3h5v.s7.ac13cf66bd9b from=translated src=- shape=805d14c1 vocab=f72abbb1
-/
lemma not_dvd_tup (dx : ↑(Y n F) ∣ x) (dF : Disjoint {0, 1, 2, 5, 10} F) :
    ∀ f ∈ F, ∀ i, ¬↑f ∣ tup n F x i := fun f hf i ↦ by
  simp_rw [disjoint_insert_left, disjoint_singleton_left] at dF
  have lf : 3 ≤ f := by
    by_contra h
    interval_cases f <;> simp_all
  cases i using Fin.addCases with
  | left i =>
    rw [tup_castAdd]
    exact_mod_cast (prime_def_lt'.mp prime_primeChain).2 _ (by lia) (lt_primeChain_of_mem_F hf)
  | right i =>
    replace dx := (dvd_of_Y_dvd dx).2.1 f (by grind)
    fin_cases i <;> simp only [reduceFinMk]
    · rw [tup_natAdd_zero]
      norm_cast
      exact ((VW n F).not_dvd _ (mem_Icc.mpr ⟨lf, le_max_iff.mpr (.inr (le_sup hf (f := id)))⟩)).1
    · rw [tup_natAdd_one, dvd_neg]
      norm_cast
      exact ((VW n F).not_dvd _ (mem_Icc.mpr ⟨lf, le_max_iff.mpr (.inr (le_sup hf (f := id)))⟩)).2
    · rw [tup_natAdd_two,
        show (x - 1) ^ 5 = (x ^ 4 - 5 * x ^ 3 + 10 * x ^ 2 - 10 * x + 5) * x - 1 by ring,
        dvd_sub_right (dx.mul_left _)]
      norm_cast
      rw [dvd_one]
      lia
    · rw [tup_natAdd_three, show 10 * (x ^ 2 + 1) ^ 2 = (10 * x ^ 3 + 20 * x) * x + 10 by ring,
        dvd_add_right (dx.mul_left _)]
      norm_cast
      obtain hf' | hf' := le_or_gt f 10
      · interval_cases f <;> lia
      · exact not_dvd_of_pos_of_lt (by decide) hf'
    · rw [tup_natAdd_four, dvd_neg,
        show (x + 1) ^ 5 = (x ^ 4 + 5 * x ^ 3 + 10 * x ^ 2 + 10 * x + 5) * x + 1 by ring,
        dvd_add_right (dx.mul_left _)]
      norm_cast
      rw [dvd_one]
      lia

end Coprime

end OddCase
