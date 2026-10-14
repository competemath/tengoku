/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import Tengoku

/-!
# IMO 2017 N6

A multiset $S$ of positive rational numbers is called *nice* if
  both $\sum_{q ∈ S} q$ and $\sum_{q ∈ S} 1/q$ are integers.
Find all $n ∈ ℕ$ such that there exists infinitely many nice multisets $S$ of size $n$.
-/

@[expose] public section

namespace IMOSL
namespace IMO2017N6

open Multiset

structure nice (S : Multiset ℚ) : Prop where
  pos : ∀ q : ℚ, q ∈ S → 0 < q
  sum_eq_int : ∃ k : ℤ, S.sum = k
  sum_inv_eq_int : ∃ k : ℤ, (S.map (·⁻¹)).sum = k

def good (n : ℕ) := {S : Multiset ℚ | card S = n ∧ nice S}.Infinite

/-! ### Preliminaries -/

/--
@isnad1 id=nice.1h1v.s3.4aa5a2e36f8b from=translated src=- shape=37087c5e vocab=ca666bde
-/
theorem nice_one_cons {S : Multiset ℚ} (h : nice S) : nice (1 ::ₘ S) where
  pos := forall_mem_cons.mpr ⟨one_pos, h.pos⟩
  sum_eq_int := by
    obtain ⟨k, h0⟩ := h.sum_eq_int
    use k + 1; rw [sum_cons, h0, Int.cast_add, add_comm, Int.cast_one]
  sum_inv_eq_int := by
    obtain ⟨k, h0⟩ := h.sum_inv_eq_int
    use k + 1; rw [map_cons, sum_cons, h0, Int.cast_add, add_comm, Int.cast_one, inv_one]

/--
@isnad1 id=iff.2h2v.s4.6fc054461cf5 from=translated src=- shape=cbc0b776 vocab=5994dbb9
-/
theorem good_iff_of_spec (hn : ¬good n) (hn0 : good n.succ) : good k ↔ n.succ ≤ k := by
  have h {m} (hm : good m) : good m.succ := by
    refine Set.infinite_of_injOn_mapsTo (λ _ _ _ _ ↦ (cons_inj_right (1 : ℚ)).mp) ?_ hm
    rintro S ⟨h, h0⟩; exact ⟨h ▸ S.card_cons 1, nice_one_cons h0⟩
  replace h {m m'} (hm : good m) : m ≤ m' → good m' :=
    Nat.le_induction hm (λ _ _ ↦ h) m'
  exact ⟨λ h0 ↦ Nat.le_of_not_lt λ h1 ↦ hn (h h0 (Nat.le_of_lt_succ h1)), h hn0⟩

/-! ### `2` is not good -/

/--
@isnad1 id=eq.1h1v.s4.5b8bc6600bae from=translated src=- shape=e3dc18fd vocab=76163806
-/
theorem rat_inv_den {q : ℚ} (h : 0 < q) : (q⁻¹.den : ℤ) = q.num := by
  rw [q.inv_def, Rat.divInt_eq_div]
  exact Rat.den_div_eq_of_coprime (Rat.num_pos.mpr h) q.reduced.symm

/--
@isnad1 id=eq.1h3v.s4.4e51056b8f6e from=translated src=- shape=397bc644 vocab=d9168f36
-/
theorem den_eq_of_add_eq_int : ∀ {q r : ℚ} {k : ℤ}, q + r = k → q.den = r.den := by
  have h {q r : ℚ} {k : ℤ} (h : q + r = k) : q.den ∣ r.den := by
    have h0 := Rat.add_den_dvd k (-r)
    rwa [Rat.den_intCast, Nat.one_mul, Rat.neg_den, ← h, add_neg_cancel_right] at h0
  intro q r k h0; exact Nat.dvd_antisymm (h h0) (h ((r.add_comm q).trans h0))

/--
@isnad1 id=or.1h1v.s4.31ddc24efd23 from=translated src=- shape=7b6444dd vocab=08c57cc2
-/
theorem nat_dvd_two_imp (hn : n ∣ 2) : n = 1 ∨ n = 2 := by
  have h : n ≤ 2 := Nat.le_of_dvd Nat.two_pos hn
  rw [Nat.le_succ_iff, Nat.le_one_iff_eq_zero_or_eq_one] at h
  refine h.imp_left (Or.resolve_left · ?_)
  rintro rfl; exact absurd hn (of_decide_eq_false rfl)

/-- This is actually an equality, but one direction is enough.
@isnad1 id=le.0h0v.s6.323c6f42ffac from=translated src=- shape=baa71c1b vocab=df1a193b
-/
theorem setOf_nice_card_two_subseteq :
    {S : Multiset ℚ | card S = 2 ∧ nice S} ⊆
      ({replicate 2 2⁻¹, replicate 2 1, replicate 2 2} : Finset (Multiset ℚ)) := by
  ---- Setup, and write `S = {x, y}` for some `x, y : ℚ`
  rintro S ⟨hS', hS, ⟨k, hS0⟩, ⟨m, hS1⟩⟩
  simp only [card_eq_two, insert_eq_cons] at hS'
  rcases hS' with ⟨x, y, rfl⟩
  rw [sum_cons, sum_singleton] at hS0
  rw [map_cons, map_singleton, sum_cons, sum_singleton] at hS1
  ---- Prove that `x = y`
  have hx : 0 < x := hS x (mem_cons_self x _)
  obtain rfl : x = y := by
    have hy : 0 < y := hS y (mem_cons_of_mem (mem_singleton_self y))
    have h := den_eq_of_add_eq_int hS1
    rw [← Int.natCast_inj, rat_inv_den hx, rat_inv_den hy] at h
    exact Rat.ext h (den_eq_of_add_eq_int hS0)
  ---- Now reduce to showing that `x ∈ {1/2, 1, 2}`
  suffices x = (2 : ℚ)⁻¹ ∨ x = 1 ∨ x = 2 by
    rw [Finset.mem_coe, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
    revert this; refine Or.imp (λ h ↦ ?_) (Or.imp (λ h ↦ ?_) (λ h ↦ ?_))
    all_goals subst x; rfl
  ---- For any `y`, if `2y` is an integer, then the denominator of `y` is `1` or `2`
  replace hS {y : ℚ} {k : ℤ} (hy : y + y = k) : y.den = 1 ∨ y.den = 2 := by
    rw [← mul_two, ← eq_div_iff_mul_eq two_ne_zero] at hy
    subst hy; rw [← Int.cast_two, ← Rat.divInt_eq_div]
    exact nat_dvd_two_imp (Int.ofNat_dvd_left.mp (Rat.den_dvd k 2))
  ---- Finally, prove that `x ∈ {1/2, 1, 2}`
  replace hS1 := hS hS1; rw [← Int.natCast_inj, ← Int.natCast_inj, rat_inv_den hx] at hS1
  replace hS0 := hS hS0; rcases hS0 with h0 | h0 <;> rcases hS1 with h1 | h1
  · right; left; exact Rat.ext h1 h0
  · right; right; exact Rat.ext h1 h0
  · left; rw [Rat.inv_def]; exact Rat.ext h1 h0
  · refine absurd x.reduced ?_
    rw [h0, h1]; exact Nat.ne_of_beq_eq_false rfl

/--
@isnad1 id=not.0h0v.s2.4a8bcf80c7c3 from=translated src=- shape=8d7dbbf6 vocab=81eab27b
-/
theorem not_good_two : ¬good 2 :=
  Set.not_infinite.mpr ((finite_toSet _).subset setOf_nice_card_two_subseteq)

/-! ### Formulas on Fibonacci numbers -/

/--
@isnad1 id=eq.0h1v.s6.bb23390ac3e7 from=translated src=- shape=e720574d vocab=3fc9a9a8
-/
theorem fib_formula1 : ∀ n, ((n + 1).fib ^ 2 : ℤ) = (n + 2).fib * n.fib + (-1) ^ n :=
  Nat.rec rfl λ n hn ↦ calc
    _ = ((n + 2).fib : ℤ) * (n.fib + (n + 1).fib : ℕ) := by rw [sq, ← Nat.fib_add_two]
    _ = (n + 2).fib * n.fib + (n + 2).fib * (n + 1).fib := by rw [Nat.cast_add, mul_add]
    _ = (n + 1).fib ^ 2 + (n + 2).fib * (n + 1).fib - (-1) ^ n := by
      rw [hn, add_right_comm, add_sub_cancel_right]
    _ = (n + 3).fib * (n + 1).fib - (-1) ^ n := by
      rw [sub_left_inj, sq, Nat.fib_add_two (n := n + 1), Nat.cast_add, add_mul]
    _ = _ := by rw [sub_eq_add_neg, ← Int.mul_neg_one, pow_succ]

/--
@isnad1 id=eq.0h1v.s6.c800607eac0c from=translated src=- shape=25578f09 vocab=2f775670
-/
theorem fib_formula2 (n) : (2 * n + 2).fib ^ 2 + 1 = (2 * n + 3).fib * (2 * n + 1).fib := by
  have h := add_neg_eq_of_eq_add (fib_formula1 (2 * n + 1))
  rwa [← Int.mul_neg_one, ← pow_succ, ← Nat.mul_succ 2, pow_mul, neg_one_sq,
    one_pow, ← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_succ, Nat.cast_inj] at h

/--
@isnad1 id=eq.0h1v.s7.b9a508004e37 from=translated src=- shape=e1540517 vocab=2f775670
-/
theorem fib_formula3 (n) :
    (2 * n + 3).fib ^ 2 + (2 * n + 1).fib ^ 2 + 1
      = 3 * ((2 * n + 3).fib * (2 * n + 1).fib) := calc
  _ = ((2 * n + 1).fib + (2 * n + 2).fib) ^ 2 + (2 * n + 1).fib ^ 2 + 1 := by
    rw [Nat.fib_add_two]
  _ = 2 * (((2 * n + 1).fib + (2 * n + 2).fib) * (2 * n + 1).fib)
      + ((2 * n + 2).fib ^ 2 + 1) := by ring
  _ = _ := by rw [← Nat.fib_add_two, fib_formula2, ← Nat.succ_mul]

/--
@isnad1 id=eq.0h1v.s7.a0ebc7d5d72b from=translated src=- shape=cb9573ff vocab=11e0c41a
-/
theorem fib_formula4 (n) :
    ((2 * n + 1).fib.succ + 1) * (2 * n + 1).fib.succ
      + (2 * n + 3).fib.succ * ((2 * n + 3).fib.succ + 1)
      = 3 * ((2 * n + 3).fib.succ * (2 * n + 1).fib.succ) := calc
  _ = (2 * n + 3).fib ^ 2 + (2 * n + 1).fib ^ 2 + 1
      + 3 * (2 * n + 3).fib + 3 * ((2 * n + 1).fib + 1) := by
    rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one]; ring
  _ = 3 * ((2 * n + 3).fib * (2 * n + 1).fib)
      + 3 * (2 * n + 3).fib + 3 * ((2 * n + 1).fib + 1) := by rw [fib_formula3]
  _ = _ := by rw [← Nat.mul_add, ← Nat.mul_succ, ← Nat.mul_add, ← Nat.succ_mul]

/--
@isnad1 id=eq.0h1v.s7.896a5d2769bc from=translated src=- shape=1f13289d vocab=28722ebe
-/
theorem fib_formula5 (n) :
    (((2 * n + 1).fib.succ + 1 : ℕ) : ℚ) / (2 * n + 3).fib.succ +
      ((2 * n + 3).fib.succ + 1 : ℕ) / (2 * n + 1).fib.succ = 3 := by
  have X (k : ℕ) : (k.fib.succ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  calc
    _ = ((((2 * n + 1).fib.succ + 1 : ℕ) : ℚ) * (2 * n + 1).fib.succ
          + (2 * n + 3).fib.succ * ((2 * n + 3).fib.succ + 1 : ℕ))
        / ((2 * n + 3).fib.succ * (2 * n + 1).fib.succ) :=
      div_add_div _ _ (X _) (X _)
    _ = (((2 * n + 1).fib.succ + 1) * (2 * n + 1).fib.succ
          + (2 * n + 3).fib.succ * ((2 * n + 3).fib.succ + 1) : ℕ)
        / ((2 * n + 3).fib.succ * (2 * n + 1).fib.succ) := by
      rw [← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_add]
    _ = (3 * ((2 * n + 3).fib.succ * (2 * n + 1).fib.succ))
        / ((2 * n + 3).fib.succ * (2 * n + 1).fib.succ) := by
      rw [fib_formula4, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_mul]
    _ = 3 := mul_div_cancel_right₀ _ (mul_ne_zero (X _) (X _))

/--
@isnad1 id=eq.0h1v.s7.c43c498acb08 from=translated src=- shape=72a825a6 vocab=28722ebe
-/
theorem fib_main_formula (n) :
    (((2 * n + 3).fib.succ + (2 * n + 1).fib.succ + 1 : ℕ) : ℚ) / (2 * n + 3).fib.succ +
      ((2 * n + 3).fib.succ + (2 * n + 1).fib.succ + 1 : ℕ) / (2 * n + 1).fib.succ = 5 :=
  calc
  _ = ((2 * n + 3).fib.succ + ((2 * n + 1).fib.succ + 1 : ℕ) : ℚ) / (2 * n + 3).fib.succ
      + ((2 * n + 1).fib.succ + ((2 * n + 3).fib.succ + 1 : ℕ)) / (2 * n + 1).fib.succ := by
    refine congrArg₂ _ ?_ ?_
    · rw [Nat.add_assoc, Nat.cast_add]
    · rw [Nat.add_assoc, Nat.add_left_comm, Nat.cast_add]
  _ = (1 + ((2 * n + 1).fib.succ + 1 : ℕ) / (2 * n + 3).fib.succ)
      + (1 + ((2 * n + 3).fib.succ + 1 : ℕ) / (2 * n + 1).fib.succ) := by
    have X (k : ℕ) : (k.fib.succ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
    rw [add_div, div_self (X _), add_div, div_self (X _)]
  _ = 5 := by rw [add_add_add_comm, fib_formula5]; norm_num

/-! ### `3` is good -/

def FibNatMultiset (n : ℕ) : Multiset ℕ :=
  {(2 * n + 3).fib.succ, (2 * n + 1).fib.succ, 1}

/--
@isnad1 id=lt.1h2v.s4.a3c69994682a from=translated src=- shape=e8bdf649 vocab=e0689963
-/
theorem FibNatMultiset_pos {n q} (hq : q ∈ FibNatMultiset n) : 0 < q := by
  rw [FibNatMultiset, insert_eq_cons, mem_cons,
    insert_eq_cons, mem_cons, mem_singleton] at hq
  rcases hq with rfl | rfl | rfl
  all_goals exact Nat.succ_pos _

/--
@isnad1 id=eq.0h1v.s6.e336daf3e352 from=translated src=- shape=1a6f1dc8 vocab=655fd9fb
-/
theorem FibNatMultiset_sum_formula (n) :
    (FibNatMultiset n).sum = (2 * n + 3).fib.succ + ((2 * n + 1).fib.succ + 1) := rfl

/--
@isnad1 id=lt.0h1v.s3.e3ed324e8966 from=translated src=- shape=b85d521b vocab=a71b9104
-/
theorem FibNatMultiset_sum_pos (n) : 0 < (FibNatMultiset n).sum :=
  Nat.add_pos_left (Nat.succ_pos _) _

/--
@isnad1 id=strictmo.0h0v.s3.ed01daf1f625 from=translated src=- shape=d53ce0fa vocab=7d0575b1
-/
theorem FibNatMultiset_sum_strictMono : StrictMono λ n ↦ (FibNatMultiset n).sum := by
  intro m n h; replace h : 2 * m + 1 < 2 * n + 1 :=
    Nat.succ_lt_succ (Nat.mul_lt_mul_of_pos_left h Nat.two_pos)
  refine Nat.add_lt_add_right (Nat.add_lt_add_of_lt_of_le ?_ ?_) 2
  exacts [Nat.succ_lt_succ (Nat.fib_add_two_strictMono h), Nat.fib_mono h.le]

def niceFibMultiset (n : ℕ) : Multiset ℚ :=
  (FibNatMultiset n).map λ r : ℕ ↦ (r : ℚ) / ((FibNatMultiset n).sum : ℚ)

/--
@isnad1 id=eq.0h1v.s3.4f48cf1819b2 from=translated src=- shape=0cfb200e vocab=0ea2c0cf
-/
theorem niceFibMultiset_card (n) : card (niceFibMultiset n) = 3 := rfl

/--
@isnad1 id=lt.1h2v.s4.083e6470a108 from=translated src=- shape=c860e20e vocab=51244ffa
-/
theorem niceFibMultiset_pos (n) : ∀ q ∈ niceFibMultiset n, 0 < q := by
  rw [niceFibMultiset, forall_mem_map_iff]
  exact λ q hq ↦ div_pos (Nat.cast_pos.mpr (FibNatMultiset_pos hq))
    (Nat.cast_pos.mpr (FibNatMultiset_sum_pos n))

/--
@isnad1 id=eq.0h1v.s3.5bd99405e0fb from=translated src=- shape=562e4a6d vocab=732de4f0
-/
theorem niceFibMultiset_sum_eq_one (n) : (niceFibMultiset n).sum = 1 := by
  rw [niceFibMultiset, FibNatMultiset]
  simp only [insert_eq_cons, sum_cons, map_cons]
  rw [map_singleton, sum_singleton, sum_singleton,
    ← add_div, ← add_div, ← Nat.cast_add, ← Nat.cast_add]
  exact div_self (Nat.cast_ne_zero.mpr (FibNatMultiset_sum_pos n).ne.symm)

/--
@isnad1 id=eq.0h1v.s7.e4da57b4120a from=translated src=- shape=52ebdff0 vocab=49c9f470
-/
theorem niceFibMultiset_inv_eq (n) :
    (niceFibMultiset n).map (·⁻¹) =
      {((FibNatMultiset n).sum : ℚ) / (2 * n + 3).fib.succ,
        ((FibNatMultiset n).sum : ℚ) / (2 * n + 1).fib.succ,
        ((FibNatMultiset n).sum : ℚ)} := calc
  _ = {(((2 * n + 3).fib.succ : ℚ) / (FibNatMultiset n).sum)⁻¹,
      (((2 * n + 1).fib.succ : ℚ) / (FibNatMultiset n).sum)⁻¹,
      ((1 : ℚ) / (FibNatMultiset n).sum)⁻¹} := rfl
  _ = _ := by simp only [inv_div]; rw [div_one]

/--
@isnad1 id=eq.0h1v.s5.9a2560db0bfe from=translated src=- shape=2e3200e1 vocab=f00ac302
-/
theorem niceFibMultiset_inv_sum_eq (n) :
    ((niceFibMultiset n).map (·⁻¹)).sum = ((FibNatMultiset n).sum + 5 : ℕ) := calc
  _ = ((FibNatMultiset n).sum : ℚ) / (2 * n + 3).fib.succ
      + ((FibNatMultiset n).sum / (2 * n + 1).fib.succ + (FibNatMultiset n).sum) := by
    rw [niceFibMultiset_inv_eq, insert_eq_cons, sum_cons,
      insert_eq_cons, sum_cons, sum_singleton]
  _ = (FibNatMultiset n).sum + 5 := by
    rw [← add_assoc, add_comm _ 5, add_left_inj]
    exact fib_main_formula n
  _ = _ := by rw [Nat.cast_add]; rfl

/--
@isnad1 id=nice.0h1v.s2.2aed2e06e2cf from=translated src=- shape=76a08d12 vocab=70a5f34c
-/
theorem niceFibMultiset_is_nice (n) : nice (niceFibMultiset n) where
  pos := niceFibMultiset_pos n
  sum_eq_int := ⟨1, niceFibMultiset_sum_eq_one n⟩
  sum_inv_eq_int := ⟨_, niceFibMultiset_inv_sum_eq n⟩

/--
@isnad1 id=injectiv.0h0v.s2.2794b05e8569 from=translated src=- shape=4b736592 vocab=0f37ab2d
-/
theorem niceFibMultiset_inj : Function.Injective niceFibMultiset := by
  intro m n h; apply congrArg (λ M ↦ (M.map (·⁻¹)).sum) at h
  rw [niceFibMultiset_inv_sum_eq, niceFibMultiset_inv_sum_eq, Nat.cast_inj] at h
  exact FibNatMultiset_sum_strictMono.injective (Nat.add_right_cancel h)

/--
@isnad1 id=good.0h0v.s2.55a08b31254a from=translated src=- shape=e590c3e1 vocab=81eab27b
-/
theorem good_three : good 3 :=
  Set.infinite_of_injective_forall_mem niceFibMultiset_inj
    λ n ↦ ⟨niceFibMultiset_card n, niceFibMultiset_is_nice n⟩

/-! ### Final solution -/

/-- Final solution
@isnad1 id=iff.0h1v.s3.07420f307b18 from=translated src=- shape=e3b88aef vocab=0b7de328
-/
theorem final_solution : good n ↔ 3 ≤ n :=
  good_iff_of_spec not_good_two good_three
