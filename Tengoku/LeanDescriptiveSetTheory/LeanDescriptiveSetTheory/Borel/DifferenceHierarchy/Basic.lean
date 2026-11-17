/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Borel.Hierarchy
import Tengoku.Seed.SetTheory.Ordinal.Arithmetic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Hausdorff difference operation

This file fixes the convention for the Hausdorff difference hierarchy.  If `A` is an increasing
family indexed below `i`, `difference i A` contains the points whose least entry stage has parity
opposite to `i`.  Ordinal parity is the parity of the finite tail: zero and nonzero limits are even,
and successor toggles parity.

With this convention the finite levels expand as

* `D₁(A) = A₀`;
* `D₂(A) = A₁ \ A₀`;
* `D₃(A) = A₀ ∪ (A₂ \ A₁)` for increasing `A`.

The operation is defined for every ordinal.  `HausdorffDifference i s` additionally records the
intended release boundary `0 < i < ω₁` and requires an increasing open family.
-/

open Ordinal Set

universe u v

namespace DescriptiveSetTheory

/-- Parity of the finite tail of an ordinal.  Zero and limit ordinals are even.-/
noncomputable def ordinalParity (i : Ordinal.{0}) : Bool :=
  Ordinal.limitRecOn i false (fun _ parity => !parity) (fun _ _ _ => false)

@[simp] theorem ordinalParity_zero : ordinalParity 0 = false := by
  simp [ordinalParity]

@[simp] theorem ordinalParity_add_one (i : Ordinal.{0}) :
    ordinalParity (i + 1) = !ordinalParity i := by
  simp [ordinalParity]

@[simp] theorem ordinalParity_one : ordinalParity 1 = true := by
  simpa using ordinalParity_add_one 0

@[simp] theorem ordinalParity_two : ordinalParity 2 = false := by
  calc
    ordinalParity 2 = ordinalParity (1 + 1) := by norm_num
    _ = !ordinalParity 1 := ordinalParity_add_one 1
    _ = false := by simp

@[simp] theorem ordinalParity_three : ordinalParity 3 = true := by
  calc
    ordinalParity 3 = ordinalParity (2 + 1) := by norm_num
    _ = !ordinalParity 2 := ordinalParity_add_one 2
    _ = true := by simp

/-- Every nonzero limit ordinal has even parity.-/
theorem ordinalParity_of_isSuccLimit {i : Ordinal.{0}} (hi : Order.IsSuccLimit i) :
    ordinalParity i = false := by
  simp [ordinalParity, hi]

/-- Left multiplication by two always has even ordinal parity.-/
@[simp] theorem ordinalParity_two_mul (i : Ordinal.{0}) :
    ordinalParity (2 * i) = false := by
  induction i using Ordinal.limitRecOn with
  | zero => simp
  | add_one i ih =>
      rw [mul_add_one]
      nth_rw 2 [show (2 : Ordinal) = 1 + 1 by norm_num]
      rw [← add_assoc]
      rw [ordinalParity_add_one, ordinalParity_add_one, ih]
      simp
  | limit i hi ih =>
      exact ordinalParity_of_isSuccLimit
        (Ordinal.isSuccLimit_mul_right (by norm_num) hi)

/-- The successor of a doubled ordinal has odd ordinal parity.-/
theorem ordinalParity_two_mul_add_one (i : Ordinal.{0}) :
    ordinalParity (2 * i + 1) = true := by
  simp

/-- The part of `A j` entering for the first time at stage `j`.-/
def differenceLayer {X : Type u} {i : Ordinal.{0}} (A : Set.Iio i → Set X)
    (j : Set.Iio i) : Set X :=
  A j \ ⋃ k : Set.Iio j.1,
    A ⟨k.1, (show k.1 < j.1 from k.2).trans (show j.1 < i from j.2)⟩

theorem mem_differenceLayer {X : Type u} {i : Ordinal.{0}} {A : Set.Iio i → Set X}
    {j : Set.Iio i} {x : X} :
    x ∈ differenceLayer A j ↔
      x ∈ A j ∧ ∀ k : Set.Iio j.1,
        x ∉ A ⟨k.1, (show k.1 < j.1 from k.2).trans (show j.1 < i from j.2)⟩ := by
  simp [differenceLayer]

/-- The Hausdorff difference operation for an ordinal-indexed family.-/
def difference {X : Type u} (i : Ordinal.{0}) (A : Set.Iio i → Set X) : Set X :=
  {x | ∃ j : Set.Iio i,
    ordinalParity j.1 ≠ ordinalParity i ∧ x ∈ differenceLayer A j}

theorem mem_difference {X : Type u} {i : Ordinal.{0}} {A : Set.Iio i → Set X} {x : X} :
    x ∈ difference i A ↔ ∃ j : Set.Iio i,
      ordinalParity j.1 ≠ ordinalParity i ∧
        x ∈ A j ∧ ∀ k : Set.Iio j.1,
          x ∉ A ⟨k.1, (show k.1 < j.1 from k.2).trans (show j.1 < i from j.2)⟩ := by
  simp [difference, mem_differenceLayer]

/-- The zero-length difference is empty.-/
@[simp] theorem difference_zero {X : Type u} (A : Set.Iio (0 : Ordinal) → Set X) :
    difference 0 A = ∅ := by
  ext x
  simp [mem_difference]

/-- The first difference level is the only member of its family.-/
theorem difference_one {X : Type u} (A : Set.Iio (1 : Ordinal) → Set X) :
    difference 1 A = A ⟨0, by norm_num⟩ := by
  ext x
  constructor
  · rw [mem_difference]
    rintro ⟨j, _, hjA, _⟩
    have hj0 : j.1 = 0 := Order.lt_one_iff.mp j.2
    have hj : j = (⟨0, by norm_num⟩ : Set.Iio (1 : Ordinal)) := by
      apply Subtype.ext
      exact hj0
    simpa [hj] using hjA
  · intro hx
    rw [mem_difference]
    refine ⟨⟨0, by norm_num⟩, by simp, hx, ?_⟩
    intro k
    have hk : k.1 < (0 : Ordinal) := k.2
    exact (not_lt_zero hk).elim

/-- At length two, only the stage-one layer has the selected parity.-/
theorem difference_two {X : Type u} (A : Set.Iio (2 : Ordinal) → Set X) :
    difference 2 A =
      A ⟨1, by norm_num⟩ \ A ⟨0, by norm_num⟩ := by
  ext x
  constructor
  · rw [mem_difference]
    rintro ⟨j, hjParity, hjA, hjLeast⟩
    have hjle : j.1 ≤ (1 : Ordinal) := by
      have hjlt : j.1 < (1 : Ordinal) + 1 := by
        rw [show (1 : Ordinal) + 1 = 2 by norm_num]
        exact j.2
      exact Order.lt_add_one_iff.mp hjlt
    have hj1 : j.1 = 1 := by
      rcases eq_or_lt_of_le hjle with hj1 | hjlt
      · exact hj1
      · have hj0 : j.1 = 0 := Order.lt_one_iff.mp hjlt
        have hparity : ordinalParity j.1 = ordinalParity 2 := by simp [hj0]
        exact (hjParity hparity).elim
    have hj : j = (⟨1, by norm_num⟩ : Set.Iio (2 : Ordinal)) := by
      apply Subtype.ext
      exact hj1
    refine ⟨by simpa [hj] using hjA, ?_⟩
    have h0j : (0 : Ordinal) < j.1 := by rw [hj1]; norm_num
    have hleast := hjLeast ⟨0, h0j⟩
    simpa [hj] using hleast
  · rintro ⟨hx1, hx0⟩
    rw [mem_difference]
    refine ⟨⟨1, by norm_num⟩, by simp, hx1, ?_⟩
    intro k
    have hk0 : k.1 = 0 := Order.lt_one_iff.mp k.2
    have hk : k = (⟨0, by norm_num⟩ : Set.Iio (1 : Ordinal)) := by
      apply Subtype.ext
      exact hk0
    simpa [hk] using hx0

/-- At length three, the selected first-entry layers are stages zero and two.-/
theorem difference_three {X : Type u} (A : Set.Iio (3 : Ordinal) → Set X)
    (hA : Monotone A) :
    difference 3 A =
      A ⟨0, by norm_num⟩ ∪
        (A ⟨2, by change (2 : Ordinal) < 2 + 1; exact Order.lt_succ 2⟩ \
          A ⟨1, by norm_num⟩) := by
  ext x
  constructor
  · rw [mem_difference]
    rintro ⟨j, hjParity, hjA, hjLeast⟩
    have hjle : j.1 ≤ (2 : Ordinal) := by
      have hjlt : j.1 < (2 : Ordinal) + 1 := by
        rw [show (2 : Ordinal) + 1 = 3 by norm_num]
        exact j.2
      exact Order.lt_add_one_iff.mp hjlt
    rcases eq_or_lt_of_le hjle with hj2 | hjlt2
    · right
      have hj : j =
          (⟨2, by change (2 : Ordinal) < 2 + 1; exact Order.lt_succ 2⟩ :
            Set.Iio (3 : Ordinal)) := by
        apply Subtype.ext
        exact hj2
      refine ⟨by simpa [hj] using hjA, ?_⟩
      have h1j : (1 : Ordinal) < j.1 := by rw [hj2]; norm_num
      have hleast := hjLeast ⟨1, h1j⟩
      simpa [hj] using hleast
    · have hjlt2' : j.1 < (1 : Ordinal) + 1 := by
        rw [show (1 : Ordinal) + 1 = 2 by norm_num]
        exact hjlt2
      have hjle1 : j.1 ≤ (1 : Ordinal) := Order.lt_add_one_iff.mp hjlt2'
      rcases eq_or_lt_of_le hjle1 with hj1 | hjlt1
      · have hparity : ordinalParity j.1 = ordinalParity 3 := by simp [hj1]
        exact (hjParity hparity).elim
      · left
        have hj0 : j.1 = 0 := Order.lt_one_iff.mp hjlt1
        have hj : j = (⟨0, by norm_num⟩ : Set.Iio (3 : Ordinal)) := by
          apply Subtype.ext
          exact hj0
        simpa [hj] using hjA
  · rintro (hx0 | ⟨hx2, hx1⟩)
    · rw [mem_difference]
      refine ⟨⟨0, by norm_num⟩, by simp, hx0, ?_⟩
      intro k
      have hk : k.1 < (0 : Ordinal) := k.2
      exact (not_lt_zero hk).elim
    · rw [mem_difference]
      refine ⟨⟨2, by change (2 : Ordinal) < 2 + 1; exact Order.lt_succ 2⟩,
        by simp, hx2, ?_⟩
      intro k
      have hklt : k.1 < (1 : Ordinal) + 1 := by
        rw [show (1 : Ordinal) + 1 = 2 by norm_num]
        exact k.2
      have hkle : k.1 ≤ (1 : Ordinal) := Order.lt_add_one_iff.mp hklt
      exact fun hk => hx1 (hA hkle hk)

/-- Membership in a successor-length difference, with the parity toggle made explicit.-/
theorem mem_difference_add_one {X : Type u} {i : Ordinal.{0}}
    {A : Set.Iio (i + 1) → Set X} {x : X} :
    x ∈ difference (i + 1) A ↔ ∃ j : Set.Iio (i + 1),
      ordinalParity j.1 = ordinalParity i ∧
        x ∈ A j ∧ ∀ k : Set.Iio j.1,
          x ∉ A ⟨k.1, (show k.1 < j.1 from k.2).trans (show j.1 < i + 1 from j.2)⟩ := by
  rw [mem_difference]
  simp only [ordinalParity_add_one, Bool.ne_not]

/-- Membership in a nonzero-limit difference: precisely the odd first-entry layers are selected.-/
theorem mem_difference_of_isSuccLimit {X : Type u} {i : Ordinal.{0}}
    (hi : Order.IsSuccLimit i) {A : Set.Iio i → Set X} {x : X} :
    x ∈ difference i A ↔ ∃ j : Set.Iio i,
      ordinalParity j.1 = true ∧
        x ∈ A j ∧ ∀ k : Set.Iio j.1,
          x ∉ A ⟨k.1, (show k.1 < j.1 from k.2).trans (show j.1 < i from j.2)⟩ := by
  rw [mem_difference, ordinalParity_of_isSuccLimit hi]
  simp only [Bool.not_eq_false]

/-- Membership in the countable Hausdorff difference hierarchy over open sets.-/
def HausdorffDifference {X : Type u} [TopologicalSpace X]
    (i : Ordinal.{0}) (s : Set X) : Prop :=
  0 < i ∧ IsCountableBorelLevel i ∧
    ∃ A : Set.Iio i → Set X, Monotone A ∧ (∀ j, IsOpen (A j)) ∧ difference i A = s

theorem HausdorffDifference.index_pos {X : Type u} [TopologicalSpace X]
    {i : Ordinal.{0}} {s : Set X} (hs : HausdorffDifference i s) : 0 < i :=
  hs.1

theorem HausdorffDifference.index_countable {X : Type u} [TopologicalSpace X]
    {i : Ordinal.{0}} {s : Set X} (hs : HausdorffDifference i s) :
    IsCountableBorelLevel i :=
  hs.2.1

theorem HausdorffDifference.exists_open_family {X : Type u} [TopologicalSpace X]
    {i : Ordinal.{0}} {s : Set X} (hs : HausdorffDifference i s) :
    ∃ A : Set.Iio i → Set X, Monotone A ∧ (∀ j, IsOpen (A j)) ∧ difference i A = s :=
  hs.2.2

end DescriptiveSetTheory
