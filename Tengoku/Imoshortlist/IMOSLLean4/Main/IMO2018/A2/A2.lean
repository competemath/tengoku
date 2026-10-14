/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import Tengoku

/-!
# IMO 2018 A2 (P2)

Let $R$ be a totally ordered commutative ring.
Find all periodic sequences $(a_k)_{k ≥ 0}$ such that for any $k ≥ 0$,
$$ a_{k + 2} = a_k a_{k + 1} + 1. $$

Original problem: Find all possible periods of such sequence.
-/

@[expose] public section

namespace IMOSL
namespace IMO2018A2

open Finset

/-! ### Extra lemmas -/

/--
@isnad1 id=eq.1h4v.s7.19c09d88f9cb from=translated src=- shape=0717c632 vocab=0455cec0
-/
lemma sum_of_periodic [AddCommMonoid M] {a : ℕ → M} (hn : a.Periodic (n + 1)) :
    ∀ d, ∑ k ∈ range (n + 1), a (k + d) = ∑ k : Fin (n + 1), a k := by
  refine Nat.rec (sum_range a) λ d hd ↦ ?_
  rw [← hd, sum_range_succ, sum_range_succ', n.add_left_comm d 1, hn, d.zero_add]
  simp only [Nat.add_succ, Nat.succ_add]

/-! ### Start of the problem -/

def good [NonAssocSemiring R] (a : ℕ → R) := ∀ k, a (k + 2) = a k * a (k + 1) + 1

section

open Fin.NatCast

variable (R) [NonAssocRing R] (d : Fin 3)

def stdGoodSeq : ℕ → R := λ n ↦ ![2, -1, -1] (n + d)

/--
@isnad1 id=good.0h2v.s4.2d519828cbff from=translated src=- shape=55bd4c71 vocab=294e77fd
-/
theorem stdGoodSeq_is_good : good (stdGoodSeq R d) := λ k ↦ by
  unfold stdGoodSeq; rw [Nat.cast_add, Nat.cast_two, Nat.cast_succ,
    add_right_comm, add_right_comm (k : Fin 3) 1 d]
  generalize (k : Fin 3) + d = c
  match c with
  | 0 => show (-1 : R) = 2 * -1 + 1; rw [two_mul, neg_add_cancel_right]
  | 1 => show (2 : R) = -1 * -1 + 1; rw [neg_mul_neg, one_mul, one_add_one_eq_two]
  | 2 => show (-1 : R) = -1 * 2 + 1; rw [mul_two, neg_add_cancel_right]

/--
@isnad1 id=periodic.0h2v.s4.284ba0d23487 from=translated src=- shape=e0f8b06f vocab=848b79bb
-/
theorem stdGoodSeq_periodic3 : (stdGoodSeq R d).Periodic 3 := λ n ↦ by
  unfold stdGoodSeq; rw [Nat.cast_add, add_right_comm]
  exact congrArg _ (add_zero _)

/--
@isnad1 id=periodic.0h3v.s5.aa83f46581d3 from=translated src=- shape=421ef962 vocab=dc1f7bf5
-/
theorem stdGoodSeq_periodic_three_mul : ∀ k, (stdGoodSeq R d).Periodic (3 * k) := by
  refine Nat.rec (λ _ ↦ rfl) (λ k hk n ↦ ?_)
  rw [Nat.mul_succ, ← Nat.add_assoc, stdGoodSeq_periodic3, hk]

/--
@isnad1 id=periodic.1h3v.s5.eb1864fbd26c from=translated src=- shape=c2a1e53a vocab=974b0c69
-/
theorem stdGoodSeq_periodic_of_three_dvd (h : 3 ∣ k) : (stdGoodSeq R d).Periodic k := by
  rcases h with ⟨k, rfl⟩; exact stdGoodSeq_periodic_three_mul R d k

open Fin.CommRing in
/--
@isnad1 id=iff.0h3v.s5.0b042255bf96 from=translated src=- shape=8d325ff2 vocab=76d33915
-/
theorem stdGoodSeq_periodic_iff_three_dvd (R)
    [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {n} :
    (stdGoodSeq R d).Periodic n ↔ 3 ∣ n := by
  refine ⟨λ h ↦ ?_, λ ⟨k, hk⟩ ↦ hk ▸ stdGoodSeq_periodic_three_mul R d k⟩
  replace h : ![2, -1, -1] n = (2 : R) := by
    specialize h (2 * d.1); unfold stdGoodSeq at h
    have X : ((2 : ℕ) : Fin 3) + 1 = 0 := rfl
    rwa [Nat.cast_add, Nat.cast_mul, Fin.cast_val_eq_self,
      add_right_comm, ← add_one_mul, X, zero_mul, zero_add] at h
  rw [← Fin.natCast_eq_zero]; generalize (n : Fin 3) = k at h ⊢
  have X : (-1 : R) ≠ 2 := by norm_num
  match k with | 0 => rfl | 1 => exact absurd h X | 2 => exact absurd h X

end

namespace good

/--
@isnad1 id=eq.1h3v.s6.4900734dde97 from=translated src=- shape=b122cd88 vocab=4c905576
-/
lemma eq1 [Semiring R] {a : ℕ → R} (ha : good a) (k) :
    a (k + 2) ^ 2 + a k = a k * a (k + 3) + a (k + 2) := by
  rw [ha (k + 1), mul_add_one (a k), add_right_comm, ← mul_assoc, ← add_one_mul, ← ha, sq]

/--
@isnad1 id=eq.2h3v.s8.7a9019b18b6b from=translated src=- shape=19684c37 vocab=38e4f7d3
-/
lemma eq2 [Semiring R] [IsCancelAdd R] {a : ℕ → R} (ha : good a) (hn : a.Periodic (n + 1)) :
    ∑ k : Fin (n + 1), a k ^ 2 = ∑ k : Fin (n + 1), a k * a (k + 3) := by
  apply add_right_cancel (b := ∑ k : Fin (n + 1), a k); calc
    _ = ∑ k ∈ range (n + 1), a (k + 2) ^ 2 + ∑ k ∈ range (n + 1), a k :=
      congrArg₂ _ (sum_of_periodic (hn.comp _) 2).symm (sum_range _).symm
    _ = ∑ k ∈ range (n + 1), (a (k + 2) ^ 2 + a k) := sum_add_distrib.symm
    _ = ∑ k ∈ range (n + 1), (a k * a (k + 3) + a (k + 2)) := by simp only [ha.eq1]
    _ = ∑ k ∈ range (n + 1), _ + ∑ k ∈ range (n + 1), _ := sum_add_distrib
    _ = _ := congrArg₂ _ (sum_range _) (sum_of_periodic hn 2)

/--
@isnad1 id=eq.2h3v.s7.8b59b6af74e2 from=translated src=- shape=76c6cc3e vocab=079763af
-/
lemma eq3 [CommRing R] {a : ℕ → R} (ha : good a) (hn : a.Periodic (n + 1)) :
    ∑ k : Fin (n + 1), (a k - a (k + 3)) ^ 2 = 0 := calc
  _ = ∑ k : Fin (n + 1), a k ^ 2 + ∑ k : Fin (n + 1), a (k + 3) ^ 2
      - ∑ k : Fin (n + 1), 2 * (a k * a (k + 3)) := by
    simp only [sub_sq', mul_assoc]
    rw [sum_sub_distrib, sum_add_distrib]
  _ = 2 * ∑ k : Fin (n + 1), a k ^ 2 - 2 * ∑ k : Fin (n + 1), a k * a (k + 3) := by
    refine congrArg₂ _ ?_ (mul_sum _ _ _).symm
    rw [two_mul, add_right_inj, ← sum_range (λ x ↦ a (x + 3) ^ 2)]
    exact sum_of_periodic (hn.comp _) 3
  _ = _ := by rw [ha.eq2 hn, sub_self]

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  {a : ℕ → R} (ha : good a) (hn : a.Periodic (n + 1))
include ha

open Fin.NatCast in
/--
@isnad1 id=ex.2h2v.s6.a1c98bb064a9 from=translated src=- shape=a25ed052 vocab=8a82f546
-/
theorem exists_eq_stdGoodSeq_of_periodic3 (h : a.Periodic 3) : ∃ d, a = stdGoodSeq R d := by
  have X {x y z : R} (h : x * y + 1 = z) (h0 : y * z + 1 = x) : y = -1 ∨ x = z := by
    replace h0 : _ - _ = _ - _ := congrArg₂ (· - ·) h h0
    rwa [add_sub_add_right_eq_sub, mul_comm, ← mul_sub, ← neg_sub x,
      ← neg_one_mul, mul_eq_mul_right_iff, sub_eq_zero] at h0
  have h0 : a 0 = a 1 * a 2 + 1 := by rw [← ha, h]
  have h1 : a 1 = a 2 * a 0 + 1 := by rw [← h 1, ha 2, h]
  replace ha : a 2 = a 0 * a 1 + 1 := ha 0
  obtain h2 | h2 : a 0 = -1 ∨ a 2 = a 1 := X h1.symm ha.symm
  all_goals obtain h3 | h3 : a 1 = -1 ∨ a 0 = a 2 := X ha.symm h0.symm
  ---- Case 1: `a_0 = a_1 = -1`
  · rw [h2, h3, neg_mul_neg, one_mul, one_add_one_eq_two] at ha
    refine ⟨1, funext λ n ↦ ?_⟩
    rw [← h.map_mod_nat, ← Fin.val_natCast, stdGoodSeq]
    match (n : Fin 3) with | 0 => exact h2 | 1 => exact h3 | 2 => exact ha
  ---- Case 2: `a_0 = a_2 = -1`
  · rw [eq_comm, h2] at h3
    rw [h2, h3, neg_mul_neg, one_mul, one_add_one_eq_two] at h1
    refine ⟨2, funext λ n ↦ ?_⟩
    rw [← h.map_mod_nat, ← Fin.val_natCast, stdGoodSeq]
    match (n : Fin 3) with | 0 => exact h2 | 1 => exact h1 | 2 => exact h3
  ---- Case 3: `a_1 = a_2 = -1`
  · rw [h3] at h2; rw [h2, h3, neg_mul_neg, one_mul, one_add_one_eq_two] at h0
    refine ⟨0, funext λ n ↦ ?_⟩
    rw [← h.map_mod_nat, ← Fin.val_natCast, stdGoodSeq]
    match (n : Fin 3) with | 0 => exact h0 | 1 => exact h3 | 2 => exact h2
  ---- Case 4: `a_0 = a_1 = a_2`
  · rw [← h2, ← h3] at h0; clear h1 ha h2 h3 X h
    replace h0 : (2 * a 0 - 1) ^ 2 + 3 = 0 := calc
      _ = 4 * (a 0 * a 0 + 1 - a 0) := by ring
      _ = 0 := by rw [← h0, sub_self, mul_zero]
    exact absurd (add_pos_of_nonneg_of_pos (sq_nonneg _) three_pos) h0.not_gt

include hn

/--
@isnad1 id=eq.2h4v.s6.43fe5ef2ff45 from=translated src=- shape=f1a272a9 vocab=fb0b57b1
-/
lemma periodic3_Fin_of_periodic (k : Fin (n + 1)) : a (k + 3) = a k := by
  have h := (sum_eq_zero_iff_of_nonneg λ k _ ↦ sq_nonneg _).mp (ha.eq3 hn) k (mem_univ k)
  rwa [sq_eq_zero_iff, sub_eq_zero, eq_comm] at h

open Fin.NatCast in
/--
@isnad1 id=periodic.2h3v.s6.e4f4413b6af3 from=translated src=- shape=dceef4f4 vocab=90b81887
-/
lemma periodic3_of_periodic : a.Periodic 3 := by
  intro m; have h := ha.periodic3_Fin_of_periodic hn m
  rwa [Fin.val_natCast, hn.map_mod_nat, ← hn.map_mod_nat,
    Nat.mod_add_mod, hn.map_mod_nat] at h

/--
@isnad1 id=dvd.2h3v.s6.fba09a285af8 from=translated src=- shape=0604f4e7 vocab=b50f72f3
-/
theorem three_dvd_period : 3 ∣ n + 1 := by
  obtain ⟨d, rfl⟩ := ha.exists_eq_stdGoodSeq_of_periodic3 (ha.periodic3_of_periodic hn)
  exact (stdGoodSeq_periodic_iff_three_dvd d R).mp hn

end good

/-! ### Final solution -/

/--
@isnad1 id=iff.0h2v.s6.0916d797143f from=translated src=- shape=0e7e40d5 vocab=18800d21
-/
theorem final_solution_general [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {a : ℕ → R} : (good a ∧ ∃ n, a.Periodic (n + 1)) ↔ ∃ d, a = stdGoodSeq R d :=
  ⟨λ ⟨ha, _, hn⟩ ↦ ha.exists_eq_stdGoodSeq_of_periodic3 (ha.periodic3_of_periodic hn),
    λ ⟨d, h⟩ ↦ h ▸ ⟨stdGoodSeq_is_good R d, 2, stdGoodSeq_periodic3 R d⟩⟩

/--
@isnad1 id=iff.0h2v.s6.bbae137e07f2 from=translated src=- shape=7a125c8e vocab=b50f72f3
-/
theorem final_solution [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {n : ℕ} :
    (∃ a : ℕ → R, good a ∧ a.Periodic (n + 1)) ↔ 3 ∣ n + 1 :=
  ⟨λ ⟨_, ha, hn⟩ ↦ ha.three_dvd_period hn,
  λ h ↦ ⟨stdGoodSeq R 0, stdGoodSeq_is_good R 0, stdGoodSeq_periodic_of_three_dvd R 0 h⟩⟩
