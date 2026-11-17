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

/--
@isnad1 id=eq.0h0v.s3.4ab20477dc01 from=translated src=- shape=d3a93718 vocab=9c1ff50a
-/
@[simp] theorem ordinalParity_zero : ordinalParity 0 = false := by
  simp [ordinalParity]

/--
@isnad1 id=eq.0h1v.s4.82e2285a1e71 from=translated src=- shape=9d55bf98 vocab=af9ae261
-/
@[simp] theorem ordinalParity_add_one (i : Ordinal.{0}) :
    ordinalParity (i + 1) = !ordinalParity i := by
  simp [ordinalParity]

/--
@isnad1 id=eq.0h0v.s3.39c71fccf3dd from=translated src=- shape=d3a93718 vocab=d7fd01ff
-/
@[simp] theorem ordinalParity_one : ordinalParity 1 = true := by
  simpa using ordinalParity_add_one 0

/--
@isnad1 id=eq.0h0v.s3.562eaf2f1b5b from=translated src=- shape=d3a93718 vocab=829dd2bf
-/
@[simp] theorem ordinalParity_two : ordinalParity 2 = false := by
  calc
    ordinalParity 2 = ordinalParity (1 + 1) := by norm_num
    _ = !ordinalParity 1 := ordinalParity_add_one 1
    _ = false := by simp

/--
@isnad1 id=eq.0h0v.s3.07f318c62973 from=translated src=- shape=d3a93718 vocab=0a2424ed
-/
@[simp] theorem ordinalParity_three : ordinalParity 3 = true := by
  calc
    ordinalParity 3 = ordinalParity (2 + 1) := by norm_num
    _ = !ordinalParity 2 := ordinalParity_add_one 2
    _ = true := by simp

/-- Every nonzero limit ordinal has even parity.
@isnad1 id=eq.1h1v.s3.621ccf206e70 from=translated src=- shape=21d929ec vocab=54bcd4b3
-/
theorem ordinalParity_of_isSuccLimit {i : Ordinal.{0}} (hi : Order.IsSuccLimit i) :
    ordinalParity i = false := by
  simp [ordinalParity, hi]

/-- Left multiplication by two always has even ordinal parity.
@isnad1 id=eq.0h1v.s4.472ae47460ea from=translated src=- shape=08e47b01 vocab=856b21c9
-/
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

/-- The successor of a doubled ordinal has odd ordinal parity.
@isnad1 id=eq.0h1v.s5.88b3072d84c6 from=translated src=- shape=571891ee vocab=880602e8
-/
theorem ordinalParity_two_mul_add_one (i : Ordinal.{0}) :
    ordinalParity (2 * i + 1) = true := by
  simp

/-- The part of `A j` entering for the first time at stage `j`.-/
def differenceLayer {X : Type u} {i : Ordinal.{0}} (A : Set.Iio i → Set X)
    (j : Set.Iio i) : Set X :=
  A j \ ⋃ k : Set.Iio j.1,
    A ⟨k.1, (show k.1 < j.1 from k.2).trans (show j.1 < i from j.2)⟩

/--
@isnad1 id=iff.0h5v.s7.3f1a1f9fdc7d from=translated src=- shape=847facf4 vocab=f94e346b
-/
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

/--
@isnad1 id=iff.0h4v.s7.01e6ef721c19 from=translated src=- shape=e53e27b3 vocab=9eacd59f
-/
theorem mem_difference {X : Type u} {i : Ordinal.{0}} {A : Set.Iio i → Set X} {x : X} :
    x ∈ difference i A ↔ ∃ j : Set.Iio i,
      ordinalParity j.1 ≠ ordinalParity i ∧
        x ∈ A j ∧ ∀ k : Set.Iio j.1,
          x ∉ A ⟨k.1, (show k.1 < j.1 from k.2).trans (show j.1 < i from j.2)⟩ := by
  simp [difference, mem_differenceLayer]

/-- The zero-length difference is empty.
@isnad1 id=eq.0h2v.s5.54c363127e52 from=translated src=- shape=e1bfec9e vocab=add54871
-/
@[simp] theorem difference_zero {X : Type u} (A : Set.Iio (0 : Ordinal) → Set X) :
    difference 0 A = ∅ := by
  ext x
  simp [mem_difference]

/-- The first difference level is the only member of its family.
@isnad1 id=eq.0h2v.s5.da63c3aa595c from=translated src=- shape=1783b805 vocab=1afcdf6f
-/
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

/-- At length two, only the stage-one layer has the selected parity.
@isnad1 id=eq.0h2v.s6.f9d6f68cb6df from=translated src=- shape=d7f64b0f vocab=639bd64c
-/
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

/-- At length three, the selected first-entry layers are stages zero and two.
@isnad1 id=eq.1h2v.s8.5914a1b09268 from=translated src=- shape=0f8a68b7 vocab=bdd2c543
-/
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

/-- Membership in a successor-length difference, with the parity toggle made explicit.
@isnad1 id=iff.0h4v.s8.a8d1b0d19ed7 from=translated src=- shape=4edc4ff8 vocab=732dd9ce
-/
theorem mem_difference_add_one {X : Type u} {i : Ordinal.{0}}
    {A : Set.Iio (i + 1) → Set X} {x : X} :
    x ∈ difference (i + 1) A ↔ ∃ j : Set.Iio (i + 1),
      ordinalParity j.1 = ordinalParity i ∧
        x ∈ A j ∧ ∀ k : Set.Iio j.1,
          x ∉ A ⟨k.1, (show k.1 < j.1 from k.2).trans (show j.1 < i + 1 from j.2)⟩ := by
  rw [mem_difference]
  simp only [ordinalParity_add_one, Bool.ne_not]

/-- Membership in a nonzero-limit difference: precisely the odd first-entry layers are selected.
@isnad1 id=iff.1h4v.s7.30338ef9f08d from=translated src=- shape=1e1bbe54 vocab=d227fb4f
-/
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

/--
@isnad1 id=lt.1h3v.s4.e629f1e2f5db from=translated src=- shape=8e18908f vocab=3a9f95a5
-/
theorem HausdorffDifference.index_pos {X : Type u} [TopologicalSpace X]
    {i : Ordinal.{0}} {s : Set X} (hs : HausdorffDifference i s) : 0 < i :=
  hs.1

/--
@isnad1 id=iscounta.1h3v.s4.91e5d0dee053 from=translated src=- shape=0c67a107 vocab=9f48d313
-/
theorem HausdorffDifference.index_countable {X : Type u} [TopologicalSpace X]
    {i : Ordinal.{0}} {s : Set X} (hs : HausdorffDifference i s) :
    IsCountableBorelLevel i :=
  hs.2.1

/--
@isnad1 id=ex.1h3v.s6.1cc4c5ac7ad5 from=translated src=- shape=6fe42933 vocab=7f7353f3
-/
theorem HausdorffDifference.exists_open_family {X : Type u} [TopologicalSpace X]
    {i : Ordinal.{0}} {s : Set X} (hs : HausdorffDifference i s) :
    ∃ A : Set.Iio i → Set X, Monotone A ∧ (∀ j, IsOpen (A j)) ∧ difference i A = s :=
  hs.2.2

end DescriptiveSetTheory
