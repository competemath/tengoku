/-
Copyright (c) 2026 Dhyan Aranha and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhyan Aranha, contributors
-/
module

public import Tengoku

/-!
# LeanPool.Monsky.Miscellaneous

Imported Lean Pool material for `LeanPool.Monsky.Miscellaneous`.
-/

@[expose] public section

namespace LeanPool.Monsky
open BigOperators
open Finset

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-
  This file includes Mathlib type lemmas that we were not able to find,
  mostly because they are quite esoteric.
-/

/-
  Some lemmas about Real.sign.
-/

/--
@isnad1 id=eq.1h2v.s4.05cfac71a202 from=translated src=- shape=a4e6127d vocab=102d8738
-/
lemma sign_mul_pos {a b : ℝ} (ha : 0 < a) : Real.sign (a * b) = Real.sign b := by
  by_cases hb₀ : 0 < b
  · rw [Real.sign_of_pos hb₀, Real.sign_of_pos (mul_pos ha hb₀)]
  · by_cases hb₁ : b < 0
    · rw [Real.sign_of_neg hb₁, Real.sign_of_neg (mul_neg_of_pos_of_neg ha hb₁)]
    · simp [(by linarith : b = 0)]

/--
@isnad1 id=lt.1h1v.s4.7d44ddd6a863 from=translated src=- shape=772470b0 vocab=b8831360
-/
lemma sign_pos' {a : ℝ} (h : Real.sign a = 1) : 0 < a := by
  by_contra hnonpos; simp only [not_lt] at hnonpos
  by_cases h0 : a = 0
  · simp_all
  · rw [Real.sign_of_neg (lt_of_le_of_ne hnonpos h0 )] at h
    linarith

/--
@isnad1 id=lt.1h1v.s4.7aa14ba6e3da from=translated src=- shape=1dda3d43 vocab=a1dedaca
-/
lemma sign_neg' {a : ℝ} (h : Real.sign a = -1) : a < 0 := by
  by_contra hnonneg; simp only [not_lt] at hnonneg
  by_cases h0 : a = 0
  · simp_all
  · rw [Real.sign_of_pos (lt_of_le_of_ne hnonneg (fun a_1 ↦ h0 a_1.symm))] at h
    linarith

/--
@isnad1 id=lt.2h2v.s5.2b75d8cec27d from=translated src=- shape=f42166c8 vocab=124c63c8
-/
lemma sign_div_pos {a b : ℝ} (hb₀ : b ≠ 0) (hs : Real.sign a = Real.sign b) :
    0 < a / b := by
  obtain hbs | hbs := Real.sign_apply_eq_of_ne_zero _ hb₀ <;> rw [hbs] at hs
  · exact div_pos_of_neg_of_neg (sign_neg' hs) (sign_neg' hbs)
  · exact div_pos (sign_pos' hs) (sign_pos' hbs)

/--
@isnad1 id=eq.0h2v.s4.9d353ec022e2 from=translated src=- shape=a13ca989 vocab=3ca8ddda
-/
lemma real_sign_mul {x y : ℝ} : Real.sign (x * y) = Real.sign x * Real.sign y := by
  obtain (hx | hx | hx) := lt_trichotomy x 0
  · calc
      (x * y).sign  = (-((-x) * y)).sign  := by congr; ring
      _             = - ((-x) * y).sign   := by rw [Real.sign_neg]
      _             = - y.sign            := by congr 1; exact sign_mul_pos (by linarith)
      _             = (-1) * y.sign       := by ring
      _             = x.sign * y.sign     := by congr; exact (Real.sign_of_neg hx).symm
  · rw [hx, zero_mul, Real.sign_zero, zero_mul]
  · rw [sign_mul_pos hx, Real.sign_of_pos hx, one_mul]

/--
@isnad1 id=eq.0h1v.s3.34bcced5e1fc from=translated src=- shape=9bfe7af5 vocab=3fe204b1
-/
lemma real_sign_involution {x : ℝ} : x.sign.sign = x.sign := by
  obtain (hx | hx | hx) := Real.sign_apply_eq x <;> (
  · rw [hx, Real.sign]
    simp
  )

/--
@isnad1 id=lt.1h1v.s5.a1255a17169f from=translated src=- shape=3f467c75 vocab=124c63c8
-/
lemma real_sign_div_self {x : ℝ} (hx : x ≠ 0) : 0 <  Real.sign x / x :=
  sign_div_pos hx real_sign_involution

/--
@isnad1 id=lt.1h1v.s4.4e2efae8e046 from=translated src=- shape=3f467c75 vocab=102d8738
-/
lemma real_sign_mul_self {x : ℝ} (hx : x ≠ 0) : 0 < (Real.sign x) * x := by
  obtain (hx' | hx') := Real.sign_apply_eq_of_ne_zero x hx <;> rw [hx']
  · simp [sign_neg' hx']
  · simp [sign_pos' hx']

/--
@isnad1 id=le.0h1v.s4.238b76c1ad0f from=translated src=- shape=38becc55 vocab=6e1a0e7c
-/
lemma real_sign_abs_le {x : ℝ} : |Real.sign x| ≤ 1 := by
  obtain (hx | hx | hx) := Real.sign_apply_eq x <;> simp [hx]

/- Other stuff. -/

/--
@isnad1 id=eq.2h3v.s5.9e453c7fb044 from=translated src=- shape=b150a8a1 vocab=c1d6fc68
-/
lemma mul_cancel {a b c : ℝ} (h : a ≠ 0) (h2 : a * b = a * c) :
        b = c := by simp_all only [ne_eq, mul_eq_mul_left_iff, or_false]

/--
@isnad1 id=eq.2h3v.s7.1a0996d6b7cc from=translated src=- shape=9239d7c2 vocab=37c5dd12
-/
lemma smul_cancel {a : ℝ} {b c : ℝ²} (h₁ : a ≠ 0) (h₂ : a • b = a • c)
    : b = c :=
  smul_right_injective ℝ² h₁ h₂

/--
@isnad1 id=eq.0h2v.s6.c894ca2fa2d8 from=translated src=- shape=9522b266 vocab=577b9a47
-/
lemma fin2_im {α : Type} [DecidableEq α] {f : Fin 2 → α}
    : Finset.image f (Finset.univ : Finset (Fin 2)) = {f 0, f 1} := by
  ext a
  simp only [mem_image, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases j <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/- This lemma is in mathlib but somehow I cannot get it to work unless it is in this form. -/
/--
@isnad1 id=iff.0h4v.s5.322d8fe700d7 from=translated src=- shape=d8a8d78a vocab=e3b0c442
-/
lemma forall_in_swap_special {α β : Type} {P : α → β → Prop} {Q : α → Prop} :
    (∀ a, Q a → ∀ b, P a b) ↔ (∀ b, ∀ a, Q a → P a b) :=
  ⟨fun h b a ha ↦ h a ha b, fun h a ha b ↦ h b a ha⟩

/--
@isnad1 id=iff.0h3v.s6.be2488d26db9 from=translated src=- shape=5c88bfae vocab=480089f2
-/
lemma forall_exists_pos_swap {α : Type} [Finite α] {P : ℝ → α → Prop}
    (h : ∀ δ a, P δ a → ∀ δ', δ' ≤ δ → P δ' a) :
    (∃ δ > 0, ∀ a, P δ a) ↔ (∀ a, ∃ δ > 0, P δ a) := by
  have : Fintype α := Fintype.ofFinite α
  constructor
  · exact fun ⟨δ,Qδ,Pδ⟩ a ↦ ⟨δ, Qδ, Pδ a⟩
  · intro ha
    by_cases hα : Nonempty α
    · choose fδ hfδ using ha
      have hS : (image fδ univ).Nonempty := by rwa [image_nonempty, univ_nonempty_iff]
      use min' (image fδ univ) hS
      refine ⟨?_,?_⟩
      · simp_all
      · intro x
        apply h (fδ x) x (hfδ x).2
        exact min'_le _ _ (mem_image_of_mem fδ (mem_univ x))
    · simp_all only [gt_iff_lt, not_nonempty_iff, IsEmpty.forall_iff, and_true, implies_true]
      use 1
      norm_num

/-- For positive `x`, there is a radius `δ > 0` within which `x + a * y` stays positive.
@isnad1 id=ex.1h2v.s6.f5d144e9d4e5 from=translated src=- shape=3d08beac vocab=3e926bfa
-/
lemma real_interval_δ {x : ℝ} (y : ℝ) (hx : 0 < x) : ∃ δ > 0, ∀ a, |a| ≤ δ → 0 < x + a * y := by
  by_cases hy : y = 0
  · exact ⟨1, by norm_num, fun a _ ↦ by rwa [hy,mul_zero,add_zero]⟩
  · have hyabs : 0 < |y| := abs_pos.mpr hy
    refine ⟨x / (2 * |y|), by positivity, ?_⟩
    intro a ha
    have hmul_abs : |a * y| ≤ x / 2 := by
      calc
        |a * y| = |a| * |y| := abs_mul a y
        _ ≤ (x / (2 * |y|)) * |y| := by gcongr
        _ = x / 2 := by field_simp [hyabs.ne']
    have hneg : -(x / 2) ≤ a * y := (abs_le.mp hmul_abs).1
    linarith

/- Pigeonhole lemma of the form that I have not been able to find. -/
/--
@isnad1 id=ex.1h4v.s5.bbf5c9f12b14 from=translated src=- shape=2cb918fb vocab=620e03c7
-/
lemma finset_infinite_pigeonhole {α β : Type} [Infinite α] {f : α → β} {B : Finset β}
    (hf : ∀ a, f a ∈ B) : ∃ b ∈ B, Set.Infinite (f⁻¹' {b}) := by
  let f_B := fun (a : α) => (⟨f a, hf a⟩ : B)
  have ⟨b, hb⟩ := Finite.exists_infinite_fiber f_B
  use b
  constructor
  · exact Finset.coe_mem b
  · convert Set.infinite_coe_iff.mp hb
    ext a
    cases b
    simp [f_B]

/--
@isnad1 id=ex.1h3v.s4.aef993315afb from=translated src=- shape=72dfe856 vocab=094768e7
-/
lemma infinite_distinct_el {α : Type} {S : Set α} (hS : Set.Infinite S) (k : α) :
    ∃ a ∈ S, a ≠ k := by
  have ⟨a, haS, ha⟩ :=  Set.Infinite.exists_notMem_finset hS ({k} : Finset α)
  exact ⟨a, haS, List.ne_of_not_mem_cons ha⟩

/--
@isnad1 id=ex.1h2v.s5.56d5f7341143 from=translated src=- shape=88aa0beb vocab=094768e7
-/
lemma infinite_imp_two_distinct_el {α : Type} {S : Set α} (hS : S.Infinite) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b := by
  have ⟨a, ha⟩ := Set.Infinite.nonempty hS
  have ⟨b, hb⟩ := infinite_distinct_el hS a
  use a, ha, b, hb.1, hb.2.symm

end Monsky
end LeanPool
