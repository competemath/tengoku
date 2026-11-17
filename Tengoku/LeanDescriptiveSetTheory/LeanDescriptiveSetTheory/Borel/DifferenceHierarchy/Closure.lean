/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Borel.DifferenceHierarchy.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Closure laws for the Hausdorff difference hierarchy

This file proves continuous-preimage compatibility and the `Δ⁰₂` upper bound.  The latter is not
obtained from Borel measurability alone: it explicitly partitions the union of an increasing open
family into its pairwise-disjoint first-entry layers and proves that both parity unions are F-sigma.
-/

open Ordinal Set

universe u v

namespace DescriptiveSetTheory

/-- First-entry layers are pairwise disjoint, without any monotonicity assumption on the family.
@isnad1 id=disjoint.1h5v.s6.f159aeebfa35 from=translated src=- shape=edfdb8c4 vocab=7dac4a9f
-/
theorem disjoint_differenceLayer {X : Type u} {i : Ordinal.{0}}
    {A : Set.Iio i → Set X} {j k : Set.Iio i} (hjk : j ≠ k) :
    Disjoint (differenceLayer A j) (differenceLayer A k) := by
  rw [Set.disjoint_left]
  intro x hxj hxk
  rcases lt_or_gt_of_ne (fun h => hjk (Subtype.ext h)) with hjk' | hkj'
  · have hnot := (mem_differenceLayer.1 hxk).2 ⟨j.1, hjk'⟩
    exact hnot (by simpa using (mem_differenceLayer.1 hxj).1)
  · have hnot := (mem_differenceLayer.1 hxj).2 ⟨k.1, hkj'⟩
    exact hnot (by simpa using (mem_differenceLayer.1 hxk).1)

/-- The first-entry layers partition the union of the source family.
@isnad1 id=eq.0h3v.s6.31e8e8ae05be from=translated src=- shape=1ec1237e vocab=d7a3dfe0
-/
theorem iUnion_differenceLayer {X : Type u} {i : Ordinal.{0}}
    (A : Set.Iio i → Set X) :
    ⋃ j, differenceLayer A j = ⋃ j, A j := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨j, hxj⟩
    exact ⟨j, (mem_differenceLayer.1 hxj).1⟩
  · rintro ⟨j, hxj⟩
    obtain ⟨m, hm, hmin⟩ :=
      wellFounded_lt.has_min {k : Set.Iio i | x ∈ A k} ⟨j, hxj⟩
    refine ⟨m, mem_differenceLayer.2 ⟨hm, ?_⟩⟩
    intro k hxk
    let k' : Set.Iio i :=
      ⟨k.1, (show k.1 < m.1 from k.2).trans (show m.1 < i from m.2)⟩
    exact hmin k' hxk k.2

/-- The difference operation is the union of the selected first-entry layers.
@isnad1 id=eq.0h3v.s6.c1ab4cd31902 from=translated src=- shape=6d6de209 vocab=e1903e19
-/
theorem difference_eq_iUnion {X : Type u} (i : Ordinal.{0})
    (A : Set.Iio i → Set X) :
    difference i A =
      ⋃ j, if ordinalParity j.1 ≠ ordinalParity i then differenceLayer A j else ∅ := by
  ext x
  change (∃ j : Set.Iio i,
      ordinalParity j.1 ≠ ordinalParity i ∧ x ∈ differenceLayer A j) ↔ _
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨j, hjParity, hxj⟩
    exact ⟨j, by simpa [hjParity] using hxj⟩
  · rintro ⟨j, hxj⟩
    by_cases hjParity : ordinalParity j.1 ≠ ordinalParity i
    · exact ⟨j, hjParity, by simpa [hjParity] using hxj⟩
    · simp [hjParity] at hxj

/-- The union of the first-entry layers not selected by `difference`.-/
def codifference {X : Type u} (i : Ordinal.{0}) (A : Set.Iio i → Set X) : Set X :=
  {x | ∃ j : Set.Iio i,
    ordinalParity j.1 = ordinalParity i ∧ x ∈ differenceLayer A j}

/--
@isnad1 id=eq.0h3v.s6.187a40c2ada3 from=translated src=- shape=daee3727 vocab=808708a4
-/
theorem codifference_eq_iUnion {X : Type u} (i : Ordinal.{0})
    (A : Set.Iio i → Set X) :
    codifference i A =
      ⋃ j, if ordinalParity j.1 = ordinalParity i then differenceLayer A j else ∅ := by
  ext x
  simp [codifference]

/-- The complement of a difference consists of points which never enter, together with the
first-entry layers of the other parity.
@isnad1 id=eq.0h3v.s6.5514eb804d27 from=translated src=- shape=0ce66a62 vocab=ec7ac53d
-/
theorem compl_difference {X : Type u} (i : Ordinal.{0})
    (A : Set.Iio i → Set X) :
    (difference i A)ᶜ = (⋃ j, A j)ᶜ ∪ codifference i A := by
  ext x
  constructor
  · intro hx
    by_cases hxu : x ∈ ⋃ j, A j
    · right
      rw [← iUnion_differenceLayer A] at hxu
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.1 hxu
      refine ⟨j, ?_, hxj⟩
      by_contra hjParity
      exact hx ⟨j, hjParity, hxj⟩
    · exact Or.inl hxu
  · rintro (hxu | ⟨j, hjParity, hxj⟩) hx
    · obtain ⟨k, _, hxk⟩ := hx
      exact hxu (Set.mem_iUnion.2 ⟨k, (mem_differenceLayer.1 hxk).1⟩)
    · obtain ⟨k, hkParity, hxk⟩ := hx
      have hjk : j ≠ k := by
        intro hjk
        subst k
        exact hkParity hjParity
      exact Set.disjoint_left.1 (disjoint_differenceLayer hjk) hxj hxk

/-- First-entry layers commute exactly with preimages.
@isnad1 id=eq.0h6v.s5.34c70437c880 from=translated src=- shape=1ee0b475 vocab=1614fbfe
-/
theorem preimage_differenceLayer {X : Type u} {Y : Type v} {i : Ordinal.{0}}
    (f : X → Y) (A : Set.Iio i → Set Y) (j : Set.Iio i) :
    f ⁻¹' differenceLayer A j = differenceLayer (fun k => f ⁻¹' A k) j := by
  ext x
  simp [mem_differenceLayer]

/-- The Hausdorff difference operation commutes exactly with arbitrary preimages.
@isnad1 id=eq.0h5v.s5.725d39e25c98 from=translated src=- shape=18a42039 vocab=36aaef65
-/
theorem preimage_difference {X : Type u} {Y : Type v} (f : X → Y)
    (i : Ordinal.{0}) (A : Set.Iio i → Set Y) :
    f ⁻¹' difference i A = difference i (fun j => f ⁻¹' A j) := by
  ext x
  simp [mem_difference]

/-- Continuous preimages preserve each Hausdorff difference level.
@isnad1 id=hausdorf.2h5v.s5.6cd54cccdb84 from=translated src=- shape=a094c1f5 vocab=22a0d2e9
-/
theorem HausdorffDifference.preimage {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {i : Ordinal.{0}} {s : Set Y}
    (hs : HausdorffDifference i s) {f : X → Y} (hf : Continuous f) :
    HausdorffDifference i (f ⁻¹' s) := by
  obtain ⟨hi, hic, A, hA, hAOpen, rfl⟩ := hs
  refine ⟨hi, hic, fun j => f ⁻¹' A j, fun _ _ hjk => preimage_mono (hA hjk),
    fun j => (hAOpen j).preimage hf, ?_⟩
  exact (preimage_difference f i A).symm

/-- Shift every source stage forward by one.  At a limit index the value is the union of all source
stages whose successors have already occurred, so openness and monotonicity are preserved.-/
def shiftDifferenceFamily {X : Type u} {i : Ordinal.{0}}
    (A : Set.Iio i → Set X) : Set.Iio (i + 1) → Set X := fun j =>
  ⋃ k : Set.Iio i, if k.1 + 1 ≤ j.1 then A k else ∅

/--
@isnad1 id=iff.0h5v.s7.0511e3437c34 from=translated src=- shape=86a855d8 vocab=e9fd712c
-/
theorem mem_shiftDifferenceFamily {X : Type u} {i : Ordinal.{0}}
    {A : Set.Iio i → Set X} {j : Set.Iio (i + 1)} {x : X} :
    x ∈ shiftDifferenceFamily A j ↔
      ∃ k : Set.Iio i, k.1 + 1 ≤ j.1 ∧ x ∈ A k := by
  simp [shiftDifferenceFamily]

/--
@isnad1 id=monotone.0h3v.s6.7ae2ee333bd3 from=translated src=- shape=28d543fc vocab=eeb0c471
-/
theorem monotone_shiftDifferenceFamily {X : Type u} {i : Ordinal.{0}}
    (A : Set.Iio i → Set X) : Monotone (shiftDifferenceFamily A) := by
  intro j k hjk x hx
  obtain ⟨m, hmj, hxm⟩ := mem_shiftDifferenceFamily.1 hx
  exact mem_shiftDifferenceFamily.2 ⟨m, hmj.trans hjk, hxm⟩

/--
@isnad1 id=isopen.1h4v.s6.0f09af9ca9f2 from=translated src=- shape=aa93729d vocab=49ac29e8
-/
theorem isOpen_shiftDifferenceFamily {X : Type u} [TopologicalSpace X]
    {i : Ordinal.{0}} {A : Set.Iio i → Set X} (hAOpen : ∀ j, IsOpen (A j))
    (j : Set.Iio (i + 1)) : IsOpen (shiftDifferenceFamily A j) := by
  apply isOpen_iUnion
  intro k
  split_ifs
  · exact hAOpen k
  · exact isOpen_empty

/-- Shifting every first-entry stage by one preserves the represented difference because both the
entry-stage parity and the total-length parity toggle.
@isnad1 id=eq.0h3v.s5.697045a9cc3f from=translated src=- shape=f36e7c64 vocab=02649362
-/
theorem difference_shiftDifferenceFamily {X : Type u} {i : Ordinal.{0}}
    (A : Set.Iio i → Set X) :
    difference (i + 1) (shiftDifferenceFamily A) = difference i A := by
  ext x
  constructor
  · rw [mem_difference]
    rintro ⟨j, hjParity, hxj, hjLeast⟩
    obtain ⟨a, haj, hxa⟩ := mem_shiftDifferenceFamily.1 hxj
    obtain ⟨m, hm, hmin⟩ :=
      wellFounded_lt.has_min {k : Set.Iio i | x ∈ A k} ⟨a, hxa⟩
    have hma : m.1 ≤ a.1 := le_of_not_gt (hmin a hxa)
    have hmaSucc : m.1 + 1 ≤ a.1 + 1 := by
      change Order.succ m.1 ≤ Order.succ a.1
      exact Order.succ_le_succ hma
    have hmj : m.1 + 1 ≤ j.1 := hmaSucc.trans haj
    have hjm : j.1 ≤ m.1 + 1 := by
      apply le_of_not_gt
      intro hmjlt
      have hmSuccLeI : m.1 + 1 ≤ i := Order.add_one_le_iff.2 m.2
      let m' : Set.Iio (i + 1) :=
        ⟨m.1 + 1, hmSuccLeI.trans_lt (Order.lt_succ i)⟩
      have hm'j : m' < j := hmjlt
      have hxShift : x ∈ shiftDifferenceFamily A m' :=
        mem_shiftDifferenceFamily.2 ⟨m, le_rfl, hm⟩
      exact (hjLeast ⟨m'.1, hm'j⟩) hxShift
    have hjEq : j.1 = m.1 + 1 := le_antisymm hjm hmj
    rw [mem_difference]
    refine ⟨m, ?_, hm, ?_⟩
    · have hjParity' : ordinalParity (m.1 + 1) ≠ ordinalParity (i + 1) := by
        simpa [hjEq] using hjParity
      simpa using hjParity'
    · intro k hxk
      let k' : Set.Iio i :=
        ⟨k.1, (show k.1 < m.1 from k.2).trans (show m.1 < i from m.2)⟩
      exact hmin k' hxk k.2
  · rw [mem_difference]
    rintro ⟨m, hmParity, hm, hmLeast⟩
    have hmSuccLeI : m.1 + 1 ≤ i := Order.add_one_le_iff.2 m.2
    let m' : Set.Iio (i + 1) :=
      ⟨m.1 + 1, hmSuccLeI.trans_lt (Order.lt_succ i)⟩
    rw [mem_difference]
    refine ⟨m', ?_, mem_shiftDifferenceFamily.2 ⟨m, le_rfl, hm⟩, ?_⟩
    · simpa [m'] using hmParity
    · intro j hxj
      obtain ⟨k, hkj, hxk⟩ := mem_shiftDifferenceFamily.1 hxj
      have hkSuccLt : k.1 + 1 < m.1 + 1 := hkj.trans_lt j.2
      have hkm : k.1 < m.1 := by
        change Order.succ k.1 < Order.succ m.1 at hkSuccLt
        exact Order.succ_lt_succ_iff.1 hkSuccLt
      exact hmLeast ⟨k.1, hkm⟩ (by simpa using hxk)

/-- Every exact countable Hausdorff level embeds in its successor exact level.
@isnad1 id=hausdorf.1h3v.s5.825739ea18b3 from=translated src=- shape=2cda295d vocab=59cd448c
-/
theorem HausdorffDifference.mono_add_one {X : Type u} [TopologicalSpace X]
    {i : Ordinal.{0}} {s : Set X} (hs : HausdorffDifference i s) :
    HausdorffDifference (i + 1) s := by
  obtain ⟨hi, hic, A, _, hAOpen, hAs⟩ := hs
  refine ⟨lt_of_le_of_lt bot_le (Order.lt_succ i),
    Cardinal.isSuccLimit_omega 1 |>.add_one_lt hic,
    shiftDifferenceFamily A, monotone_shiftDifferenceFamily A,
    isOpen_shiftDifferenceFamily hAOpen, ?_⟩
  rw [difference_shiftDifferenceFamily, hAs]

/-- Extend a source family to a larger ordinal by keeping the union of all source stages already
reached.  Points retain their original first-entry stage.-/
def extendDifferenceFamily {X : Type u} {i : Ordinal.{0}} (k : Ordinal.{0})
    (A : Set.Iio i → Set X) : Set.Iio k → Set X := fun j =>
  ⋃ a : Set.Iio i, if a.1 ≤ j.1 then A a else ∅

/--
@isnad1 id=iff.0h6v.s6.78f3b48b379d from=translated src=- shape=f2157752 vocab=8dc183a7
-/
theorem mem_extendDifferenceFamily {X : Type u} {i k : Ordinal.{0}}
    {A : Set.Iio i → Set X} {j : Set.Iio k} {x : X} :
    x ∈ extendDifferenceFamily k A j ↔ ∃ a : Set.Iio i, a.1 ≤ j.1 ∧ x ∈ A a := by
  simp [extendDifferenceFamily]

/--
@isnad1 id=monotone.0h4v.s6.66f4b510a33a from=translated src=- shape=e4d372cb vocab=10b07715
-/
theorem monotone_extendDifferenceFamily {X : Type u} {i k : Ordinal.{0}}
    (A : Set.Iio i → Set X) : Monotone (extendDifferenceFamily k A) := by
  intro j l hjl x hx
  obtain ⟨a, haj, hxa⟩ := mem_extendDifferenceFamily.1 hx
  exact mem_extendDifferenceFamily.2 ⟨a, haj.trans hjl, hxa⟩

/--
@isnad1 id=isopen.1h5v.s5.a9bf2b02b635 from=translated src=- shape=310dc5ca vocab=dfedae60
-/
theorem isOpen_extendDifferenceFamily {X : Type u} [TopologicalSpace X]
    {i k : Ordinal.{0}} {A : Set.Iio i → Set X} (hAOpen : ∀ j, IsOpen (A j))
    (j : Set.Iio k) : IsOpen (extendDifferenceFamily k A j) := by
  apply isOpen_iUnion
  intro a
  split_ifs
  · exact hAOpen a
  · exact isOpen_empty

/-- Extending a family to a larger ordinal of the same parity preserves its difference.
@isnad1 id=eq.2h4v.s5.95c7af7956ca from=translated src=- shape=581bc5ea vocab=d3164321
-/
theorem difference_extendDifferenceFamily {X : Type u} {i k : Ordinal.{0}}
    (hik : i ≤ k) (hParity : ordinalParity i = ordinalParity k)
    (A : Set.Iio i → Set X) :
    difference k (extendDifferenceFamily k A) = difference i A := by
  ext x
  constructor
  · rw [mem_difference]
    rintro ⟨j, hjParity, hxj, hjLeast⟩
    obtain ⟨a, haj, hxa⟩ := mem_extendDifferenceFamily.1 hxj
    obtain ⟨m, hm, hmin⟩ :=
      wellFounded_lt.has_min {b : Set.Iio i | x ∈ A b} ⟨a, hxa⟩
    have hma : m.1 ≤ a.1 := le_of_not_gt (hmin a hxa)
    have hmj : m.1 ≤ j.1 := hma.trans haj
    have hjm : j.1 ≤ m.1 := by
      apply le_of_not_gt
      intro hmjlt
      have hmk : m.1 < k := m.2.trans_le hik
      let m' : Set.Iio k := ⟨m.1, hmk⟩
      have hm'j : m' < j := hmjlt
      have hxm' : x ∈ extendDifferenceFamily k A m' :=
        mem_extendDifferenceFamily.2 ⟨m, le_rfl, hm⟩
      exact (hjLeast ⟨m'.1, hm'j⟩) hxm'
    have hjEq : j.1 = m.1 := le_antisymm hjm hmj
    rw [mem_difference]
    refine ⟨m, ?_, hm, ?_⟩
    · simpa [hjEq, hParity] using hjParity
    · intro b hxb
      let b' : Set.Iio i :=
        ⟨b.1, (show b.1 < m.1 from b.2).trans (show m.1 < i from m.2)⟩
      exact hmin b' hxb b.2
  · rw [mem_difference]
    rintro ⟨m, hmParity, hm, hmLeast⟩
    have hmk : m.1 < k := m.2.trans_le hik
    let m' : Set.Iio k := ⟨m.1, hmk⟩
    rw [mem_difference]
    refine ⟨m', ?_, mem_extendDifferenceFamily.2 ⟨m, le_rfl, hm⟩, ?_⟩
    · simpa [m', hParity] using hmParity
    · intro j hxj
      obtain ⟨a, haj, hxa⟩ := mem_extendDifferenceFamily.1 hxj
      have ham : a.1 < m.1 := haj.trans_lt j.2
      exact hmLeast ⟨a.1, ham⟩ (by simpa using hxa)

/-- Exact Hausdorff difference classes are monotone in their countable ordinal index.
@isnad1 id=hausdorf.3h4v.s5.d733baeed85c from=translated src=- shape=6a9938d5 vocab=fded0e16
-/
theorem HausdorffDifference.mono {X : Type u} [TopologicalSpace X]
    {i k : Ordinal.{0}} (hik : i ≤ k) (hk : IsCountableBorelLevel k) {s : Set X}
    (hs : HausdorffDifference i s) : HausdorffDifference k s := by
  rcases eq_or_lt_of_le hik with rfl | hik'
  · exact hs
  · have hsSucc := HausdorffDifference.mono_add_one hs
    obtain ⟨hi, _, A, _, hAOpen, hAs⟩ := hs
    by_cases hParity : ordinalParity i = ordinalParity k
    · refine ⟨hi.trans_le hik, ?_, extendDifferenceFamily k A,
        monotone_extendDifferenceFamily A, isOpen_extendDifferenceFamily hAOpen, ?_⟩
      · exact hk
      · rw [difference_extendDifferenceFamily hik hParity, hAs]
    · have hiSuccLe : i + 1 ≤ k := Order.add_one_le_iff.2 hik'
      have hParitySucc : ordinalParity (i + 1) = ordinalParity k := by
        rw [ordinalParity_add_one]
        cases hiParity : ordinalParity i <;> cases hkParity : ordinalParity k <;>
          simp [hiParity, hkParity] at hParity ⊢
      obtain ⟨_, _, B, _, hBOpen, hBs⟩ := hsSucc
      refine ⟨hi.trans_le hik, hk,
        extendDifferenceFamily k B, monotone_extendDifferenceFamily B,
        isOpen_extendDifferenceFamily hBOpen, ?_⟩
      rw [difference_extendDifferenceFamily hiSuccLe hParitySucc, hBs]

private theorem ordinalSigma0_two_empty {X : Type u} [TopologicalSpace X]
    [PerfectlyNormalSpace X] : OrdinalSigma0 2 (∅ : Set X) :=
  ordinalSigma0_of_isClopen (by norm_num) isOpen_empty isClosed_empty

private theorem ordinalSigma0_two_of_isClosed {X : Type u} [TopologicalSpace X]
    {s : Set X} (hs : IsClosed s) : OrdinalSigma0 2 s := by
  rw [ordinalSigma0_two_iff_eq_iUnion_isClosed]
  refine ⟨fun _ => s, fun _ => hs, ?_⟩
  ext x
  simp

private theorem OrdinalSigma0.iUnion_countable {X : Type u} [TopologicalSpace X]
    [PerfectlyNormalSpace X] {ι : Type*} [Countable ι] {s : ι → Set X}
    (hs : ∀ a, OrdinalSigma0 2 (s a)) : OrdinalSigma0 2 (⋃ a, s a) := by
  classical
  obtain ⟨e, he⟩ := Countable.exists_injective_nat ι
  let g : ℕ → Set X := fun n => ⋃ a : ι, ⋃ (_ : e a = n), s a
  have hg : ∀ n, OrdinalSigma0 2 (g n) := by
    intro n
    by_cases hn : ∃ a, e a = n
    · obtain ⟨a, ha⟩ := hn
      have hga : g n = s a := by
        ext x
        simp only [g, Set.mem_iUnion]
        constructor
        · rintro ⟨b, hb, hxb⟩
          have hba : b = a := he (hb.trans ha.symm)
          simpa [hba] using hxb
        · intro hxa
          exact ⟨a, ha, hxa⟩
      rw [hga]
      exact hs a
    · have hge : g n = ∅ := by
        ext x
        simp only [g, Set.mem_iUnion]
        constructor
        · rintro ⟨a, ha, _⟩
          exact (hn ⟨a, ha⟩).elim
        · intro hx
          simp at hx
      rw [hge]
      exact ordinalSigma0_two_empty
  have hUnion : (⋃ a, s a) = ⋃ n, g n := by
    ext x
    simp only [g, Set.mem_iUnion]
    constructor
    · rintro ⟨a, hxa⟩
      exact ⟨e a, a, rfl, hxa⟩
    · rintro ⟨_, a, _, hxa⟩
      exact ⟨a, hxa⟩
  rw [hUnion]
  exact OrdinalSigma0.iUnion hg

private theorem differenceLayer_ordinalSigma0_two {X : Type u} [TopologicalSpace X]
    [PerfectlyNormalSpace X] {i : Ordinal.{0}} (A : Set.Iio i → Set X)
    (hAOpen : ∀ j, IsOpen (A j)) (j : Set.Iio i) :
    OrdinalSigma0 2 (differenceLayer A j) := by
  rw [show differenceLayer A j =
      A j ∩ (⋃ k : Set.Iio j.1,
        A ⟨k.1, (show k.1 < j.1 from k.2).trans (show j.1 < i from j.2)⟩)ᶜ by
    simp [differenceLayer, sdiff_eq]]
  apply OrdinalSigma0.inter
  · exact (ordinalSigma0_one_iff.2 (hAOpen j)).mono (by norm_num)
  · apply ordinalSigma0_two_of_isClosed
    exact (isOpen_iUnion fun (k : Set.Iio j.1) => hAOpen
      ⟨k.1, (show k.1 < j.1 from k.2).trans (show j.1 < i from j.2)⟩).isClosed_compl

/-- Every countable Hausdorff difference of open sets lies in `Δ⁰₂`.
@isnad1 id=ordinald.1h3v.s5.edc7956d51e3 from=translated src=- shape=e27288e3 vocab=82fb4330
-/
theorem HausdorffDifference.ordinalDelta0_two {X : Type u} [TopologicalSpace X]
    [PerfectlyNormalSpace X] {i : Ordinal.{0}} {s : Set X}
    (hs : HausdorffDifference i s) : OrdinalDelta0 2 s := by
  obtain ⟨_, hic, A, _, hAOpen, rfl⟩ := hs
  letI := countable_Iio_of_isCountableBorelLevel hic
  have hLayer : ∀ j, OrdinalSigma0 2 (differenceLayer A j) :=
    differenceLayer_ordinalSigma0_two A hAOpen
  have hSigma : OrdinalSigma0 2 (difference i A) := by
    rw [difference_eq_iUnion]
    apply OrdinalSigma0.iUnion_countable
    intro j
    split_ifs
    · exact hLayer j
    · exact ordinalSigma0_two_empty
  have hComplSigma : OrdinalSigma0 2 (difference i A)ᶜ := by
    rw [compl_difference]
    apply OrdinalSigma0.union
    · apply ordinalSigma0_two_of_isClosed
      exact (isOpen_iUnion hAOpen).isClosed_compl
    · rw [codifference_eq_iUnion]
      apply OrdinalSigma0.iUnion_countable
      intro j
      split_ifs
      · exact hLayer j
      · exact ordinalSigma0_two_empty
  exact ⟨hSigma, (ordinalSigma0_compl_iff_pi0 2 (difference i A)).1 hComplSigma⟩

/-- Append the whole space at the final successor stage.-/
def appendUnivDifferenceFamily {X : Type u} {i : Ordinal.{0}}
    (A : Set.Iio i → Set X) : Set.Iio (i + 1) → Set X := fun j =>
  if hj : j.1 < i then A ⟨j.1, hj⟩ else Set.univ

/--
@isnad1 id=monotone.1h3v.s7.ad012bf1b60f from=translated src=- shape=3ce52e66 vocab=15b89693
-/
theorem monotone_appendUnivDifferenceFamily {X : Type u} {i : Ordinal.{0}}
    {A : Set.Iio i → Set X} (hA : Monotone A) :
    Monotone (appendUnivDifferenceFamily A) := by
  intro j k hjk
  by_cases hk : k.1 < i
  · have hjkVal : j.1 ≤ k.1 := hjk
    have hj : j.1 < i := hjkVal.trans_lt hk
    simp only [appendUnivDifferenceFamily, dite_eq_left hj, dite_eq_left hk]
    exact hA hjkVal
  · simp [appendUnivDifferenceFamily, hk]

/--
@isnad1 id=isopen.1h4v.s6.993047fff7e9 from=translated src=- shape=aa93729d vocab=8bf24d5b
-/
theorem isOpen_appendUnivDifferenceFamily {X : Type u} [TopologicalSpace X]
    {i : Ordinal.{0}} {A : Set.Iio i → Set X} (hA : ∀ j, IsOpen (A j))
    (j : Set.Iio (i + 1)) : IsOpen (appendUnivDifferenceFamily A j) := by
  simp only [appendUnivDifferenceFamily]
  split_ifs
  · exact hA _
  · exact isOpen_univ

/-- Appending the whole space at the final stage represents the complement difference.
@isnad1 id=eq.0h3v.s5.599d7135e9a1 from=translated src=- shape=51debb7d vocab=92e6c935
-/
theorem difference_appendUnivDifferenceFamily {X : Type u} {i : Ordinal.{0}}
    (A : Set.Iio i → Set X) :
    difference (i + 1) (appendUnivDifferenceFamily A) = (difference i A)ᶜ := by
  rw [compl_difference]
  ext x
  constructor
  · rw [mem_difference]
    rintro ⟨j, hjParity, hxj, hjLeast⟩
    by_cases hji : j.1 < i
    · right
      refine ⟨⟨j.1, hji⟩, ?_, ?_⟩
      · have hp : ordinalParity j.1 = ordinalParity i := by
          simpa only [ordinalParity_add_one, Bool.ne_not] using hjParity
        exact hp
      · rw [mem_differenceLayer]
        refine ⟨?_, ?_⟩
        · simpa [appendUnivDifferenceFamily, hji] using hxj
        · intro k
          let k' : Set.Iio j.1 := ⟨k.1, k.2⟩
          have hkI : k.1 < i := k.2.trans hji
          have hnot := hjLeast k'
          simpa [appendUnivDifferenceFamily, hkI, k'] using hnot
    · left
      have hjiLe : j.1 ≤ i := Order.lt_add_one_iff.mp j.2
      have hjiEq : j.1 = i := le_antisymm hjiLe (le_of_not_gt hji)
      intro hxUnion
      obtain ⟨k, hxk⟩ := Set.mem_iUnion.1 hxUnion
      have hkj : k.1 < j.1 := by
        rw [hjiEq]
        exact k.2
      let k' : Set.Iio j.1 := ⟨k.1, hkj⟩
      have hnot := hjLeast k'
      apply hnot
      change x ∈ if hk : k.1 < i then A ⟨k.1, hk⟩ else Set.univ
      simp only [dite_eq_left (show k.1 < i from k.2)]
      exact hxk
  · rintro (hxOutside | hxCo)
    · rw [mem_difference]
      let j : Set.Iio (i + 1) := ⟨i, Order.lt_succ i⟩
      refine ⟨j, by simp [j], ?_, ?_⟩
      · simp [appendUnivDifferenceFamily, j]
      · intro k hxk
        have hki : k.1 < i := by
          have hk := k.2
          change k.1 < j.1 at hk
          simpa only [j] using hk
        have hxA : x ∈ A ⟨k.1, hki⟩ := by
          simpa [appendUnivDifferenceFamily, hki] using hxk
        exact hxOutside (Set.mem_iUnion.2 ⟨⟨k.1, hki⟩, hxA⟩)
    · obtain ⟨j, hjParity, hxj⟩ := hxCo
      rw [mem_differenceLayer] at hxj
      rw [mem_difference]
      let j' : Set.Iio (i + 1) := ⟨j.1, j.2.trans (Order.lt_succ i)⟩
      refine ⟨j', ?_, ?_, ?_⟩
      · simp [j', hjParity]
      · change x ∈ if hj : j.1 < i then A ⟨j.1, hj⟩ else Set.univ
        split
        · exact hxj.1
        · rename_i h
          exact (h j.2).elim
      · intro k
        let k' : Set.Iio j.1 := ⟨k.1, k.2⟩
        have hki : k.1 < i := k.2.trans j.2
        have hnot := hxj.2 k'
        simpa [appendUnivDifferenceFamily, hki, j', k'] using hnot

/-- The complement of an exact level-`i` difference belongs to exact level `i + 1`.
@isnad1 id=hausdorf.1h3v.s5.d96af41d1c3f from=translated src=- shape=c6e66fe2 vocab=195d9d72
-/
theorem HausdorffDifference.compl_add_one {X : Type u} [TopologicalSpace X]
    {i : Ordinal.{0}} {s : Set X} (hs : HausdorffDifference i s) :
    HausdorffDifference (i + 1) sᶜ := by
  obtain ⟨hi, hic, A, hA, hAOpen, hAs⟩ := hs
  refine ⟨lt_of_le_of_lt bot_le (Order.lt_succ i),
    Cardinal.isSuccLimit_omega 1 |>.add_one_lt hic,
    appendUnivDifferenceFamily A,
    monotone_appendUnivDifferenceFamily hA,
    isOpen_appendUnivDifferenceFamily hAOpen, ?_⟩
  rw [difference_appendUnivDifferenceFamily, hAs]

/-- The cumulative envelope of the exact Hausdorff levels.  This is useful for rank bounds and is
monotone by definition; it is deliberately named separately from the exact source class.-/
def HausdorffDifferenceAtMost {X : Type u} [TopologicalSpace X]
    (i : Ordinal.{0}) (s : Set X) : Prop :=
  ∃ j : Ordinal.{0}, j ≤ i ∧ HausdorffDifference j s

/-- An exact difference representation gives the corresponding cumulative bound.
@isnad1 id=hausdorf.1h3v.s4.a57592c79ce2 from=translated src=- shape=091c1afb vocab=11b5f4f8
-/
theorem HausdorffDifference.atMost {X : Type u} [TopologicalSpace X]
    {i : Ordinal.{0}} {s : Set X} (hs : HausdorffDifference i s) :
    HausdorffDifferenceAtMost i s :=
  ⟨i, le_rfl, hs⟩

/-- Cumulative Hausdorff difference bounds are monotone in the ordinal bound.
@isnad1 id=hausdorf.2h4v.s5.b620f2ca4ca0 from=translated src=- shape=51c81bcb vocab=084fc2e3
-/
theorem HausdorffDifferenceAtMost.mono {X : Type u} [TopologicalSpace X]
    {i k : Ordinal.{0}} (hik : i ≤ k) {s : Set X}
    (hs : HausdorffDifferenceAtMost i s) : HausdorffDifferenceAtMost k s := by
  obtain ⟨j, hji, hj⟩ := hs
  exact ⟨j, hji.trans hik, hj⟩

/-- Every cumulative countable difference bound is still an ambiguous level-two Borel set.
@isnad1 id=ordinald.1h3v.s5.6c81ce87bac8 from=translated src=- shape=e27288e3 vocab=32691c79
-/
theorem HausdorffDifferenceAtMost.ordinalDelta0_two {X : Type u} [TopologicalSpace X]
    [PerfectlyNormalSpace X] {i : Ordinal.{0}} {s : Set X}
    (hs : HausdorffDifferenceAtMost i s) : OrdinalDelta0 2 s := by
  obtain ⟨_, _, hj⟩ := hs
  exact hj.ordinalDelta0_two

/-- Every countable Hausdorff difference of open sets is Borel measurable.
@isnad1 id=measurab.1h3v.s4.abf9ce6d2129 from=translated src=- shape=3c339a0b vocab=0da99819
-/
theorem HausdorffDifference.measurableSet {X : Type u} [TopologicalSpace X]
    [PerfectlyNormalSpace X] {i : Ordinal.{0}} {s : Set X}
    (hs : HausdorffDifference i s) : @MeasurableSet X (borel X) s :=
  hs.ordinalDelta0_two.measurableSet

end DescriptiveSetTheory
