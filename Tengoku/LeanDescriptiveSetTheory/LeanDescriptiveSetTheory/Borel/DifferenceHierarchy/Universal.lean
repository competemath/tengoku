/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Borel.DifferenceHierarchy.Exhaustion
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Universal.BaireParameters
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Universal.Operations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Universal relations for exact Hausdorff difference levels

For a positive countable ordinal `i`, a single Baire or Cantor parameter codes an `i`-sequence of
open sets.  Taking cumulative unions makes the coded family increasing.  The resulting difference
relation is universal for `HausdorffDifference i`; its vertical sections are exactly the sets at
that exact level.
-/

open Cardinal Ordinal Set TopologicalSpace

universe u

namespace DescriptiveSetTheory

/-- A surjective sequence through every stage below a positive countable ordinal.-/
noncomputable def differenceLevelSequence (i : Ordinal.{0})
    (hi : 0 < i) (hic : IsCountableBorelLevel i) : ℕ → Set.Iio i := by
  letI : Countable (Set.Iio i) := countable_Iio_of_isCountableBorelLevel hic
  exact Set.enumerateCountable Set.countable_univ ⟨0, hi⟩

/--
@isnad1 id=surjecti.2h1v.s5.ec1019171812 from=translated src=- shape=38635126 vocab=8eb6438c
-/
theorem surjective_differenceLevelSequence (i : Ordinal.{0})
    (hi : 0 < i) (hic : IsCountableBorelLevel i) :
    Function.Surjective (differenceLevelSequence i hi hic) := by
  letI : Countable (Set.Iio i) := countable_Iio_of_isCountableBorelLevel hic
  rw [← Set.range_eq_univ]
  simpa [differenceLevelSequence] using
    (Set.range_enumerateCountable_of_mem (Set.countable_univ :
      (Set.univ : Set (Set.Iio i)).Countable)
      (Set.mem_univ (⟨0, hi⟩ : Set.Iio i)))

/-! ## Baire parameters -/

/-- The open relation coded by component `n` of a Baire parameter.-/
def baireDifferenceOpenComponent {X : Type u} (b : ℕ → Set X) (n : ℕ) :
    Set ((ℕ → ℕ) × X) :=
  (fun q => (baireUnpack q.1 n, q.2)) ⁻¹' baireParameterUniversalOpen b

/--
@isnad1 id=isopen.1h3v.s5.b3d41a90d620 from=translated src=- shape=bc3d6e4d vocab=4fece132
-/
theorem isOpen_baireDifferenceOpenComponent {X : Type u} [TopologicalSpace X]
    {b : ℕ → Set X} (hb : ∀ n, IsOpen (b n)) (n : ℕ) :
    IsOpen (baireDifferenceOpenComponent b n) := by
  exact (isOpen_baireParameterUniversalOpen hb).preimage
    (((continuous_baireUnpack n).comp continuous_fst).prodMk continuous_snd)

/-- The cumulative universal open family at a fixed difference length.-/
noncomputable def baireUniversalDifferenceFamily {X : Type u}
    (b : ℕ → Set X) (i : Ordinal.{0}) (hi : 0 < i)
    (hic : IsCountableBorelLevel i) : Set.Iio i → Set ((ℕ → ℕ) × X) := fun j =>
  ⋃ n, if (differenceLevelSequence i hi hic n).1 ≤ j.1 then
    baireDifferenceOpenComponent b n else ∅

/--
@isnad1 id=iff.2h5v.s7.d5d6aca12b30 from=translated src=- shape=7c0ff8ff vocab=a5399e24
-/
theorem mem_baireUniversalDifferenceFamily {X : Type u}
    {b : ℕ → Set X} {i : Ordinal.{0}} {hi : 0 < i}
    {hic : IsCountableBorelLevel i} {j : Set.Iio i} {q : (ℕ → ℕ) × X} :
    q ∈ baireUniversalDifferenceFamily b i hi hic j ↔
      ∃ n, (differenceLevelSequence i hi hic n).1 ≤ j.1 ∧
        q ∈ baireDifferenceOpenComponent b n := by
  simp [baireUniversalDifferenceFamily]

/--
@isnad1 id=monotone.2h3v.s6.90ee085a3e6a from=translated src=- shape=f567f702 vocab=98d782a1
-/
theorem monotone_baireUniversalDifferenceFamily {X : Type u}
    (b : ℕ → Set X) (i : Ordinal.{0}) (hi : 0 < i)
    (hic : IsCountableBorelLevel i) :
    Monotone (baireUniversalDifferenceFamily b i hi hic) := by
  intro j k hjk q hq
  obtain ⟨n, hnj, hqn⟩ := mem_baireUniversalDifferenceFamily.1 hq
  exact mem_baireUniversalDifferenceFamily.2 ⟨n, hnj.trans hjk, hqn⟩

/--
@isnad1 id=isopen.3h4v.s6.9d7cd43d43b1 from=translated src=- shape=3326e716 vocab=60aafd12
-/
theorem isOpen_baireUniversalDifferenceFamily {X : Type u}
    [TopologicalSpace X] {b : ℕ → Set X} (hb : ∀ n, IsOpen (b n))
    (i : Ordinal.{0}) (hi : 0 < i) (hic : IsCountableBorelLevel i)
    (j : Set.Iio i) : IsOpen (baireUniversalDifferenceFamily b i hi hic j) := by
  apply isOpen_iUnion
  intro n
  split_ifs
  · exact isOpen_baireDifferenceOpenComponent hb n
  · exact isOpen_empty

/-- The Baire-parameter universal relation for exact length-`i` Hausdorff differences.-/
noncomputable def baireUniversalDifference {X : Type u} (b : ℕ → Set X)
    (i : Ordinal.{0}) (hi : 0 < i) (hic : IsCountableBorelLevel i) :
    Set ((ℕ → ℕ) × X) :=
  difference i (baireUniversalDifferenceFamily b i hi hic)

/--
@isnad1 id=hausdorf.3h3v.s6.9ed8b4f86ce7 from=translated src=- shape=fabd8972 vocab=04f1c356
-/
theorem hausdorffDifference_baireUniversalDifference {X : Type u}
    [TopologicalSpace X] {b : ℕ → Set X} (hb : ∀ n, IsOpen (b n))
    {i : Ordinal.{0}} (hi : 0 < i) (hic : IsCountableBorelLevel i) :
    HausdorffDifference i (baireUniversalDifference b i hi hic) := by
  exact ⟨hi, hic, baireUniversalDifferenceFamily b i hi hic,
    monotone_baireUniversalDifferenceFamily b i hi hic,
    isOpen_baireUniversalDifferenceFamily hb i hi hic, rfl⟩

/--
@isnad1 id=iff.2h6v.s7.909d2569c70a from=translated src=- shape=eaece8d5 vocab=c4ed45d6
-/
theorem mem_verticalSection_baireUniversalDifferenceFamily {X : Type u}
    {b : ℕ → Set X} {i : Ordinal.{0}} {hi : 0 < i}
    {hic : IsCountableBorelLevel i} {j : Set.Iio i} {p : ℕ → ℕ} {x : X} :
    x ∈ verticalSection (baireUniversalDifferenceFamily b i hi hic j) p ↔
      ∃ n, (differenceLevelSequence i hi hic n).1 ≤ j.1 ∧
        x ∈ verticalSection (baireParameterUniversalOpen b) (baireUnpack p n) := by
  simp [verticalSection, baireDifferenceOpenComponent,
    baireUniversalDifferenceFamily]

/--
@isnad1 id=eq.2h4v.s6.c3b732a0725a from=translated src=- shape=d46fe9cf vocab=eadb581a
-/
theorem verticalSection_baireUniversalDifference {X : Type u}
    {b : ℕ → Set X} {i : Ordinal.{0}} {hi : 0 < i}
    {hic : IsCountableBorelLevel i} (p : ℕ → ℕ) :
    verticalSection (baireUniversalDifference b i hi hic) p =
      difference i (fun j =>
        verticalSection (baireUniversalDifferenceFamily b i hi hic j) p) := by
  have hpre := preimage_difference (fun x : X => (p, x)) i
    (baireUniversalDifferenceFamily b i hi hic)
  ext x
  change x ∈ (fun y : X => (p, y)) ⁻¹'
      difference i (baireUniversalDifferenceFamily b i hi hic) ↔
    x ∈ difference i (fun j => (fun y : X => (p, y)) ⁻¹'
      baireUniversalDifferenceFamily b i hi hic j)
  exact Set.ext_iff.mp hpre x

/-- The Baire-parameter relation is universal for the exact level `i`.
@isnad1 id=isuniver.3h3v.s5.44d16620e7a9 from=translated src=- shape=a249a58e vocab=612ccd40
-/
theorem isUniversalFor_baireUniversalDifference {X : Type u}
    [TopologicalSpace X] {b : ℕ → Set X}
    (hb : IsTopologicalBasis (Set.range b)) {i : Ordinal.{0}}
    (hi : 0 < i) (hic : IsCountableBorelLevel i) :
    IsUniversalFor (HausdorffDifference i)
      (baireUniversalDifference b i hi hic) := by
  intro s
  constructor
  · intro hs
    obtain ⟨_, _, A, hA, hAOpen, hAs⟩ := hs
    have hUniversal := isUniversalFor_baireParameterUniversalOpen hb
    choose c hc using fun j => (hUniversal (A j)).1 (hAOpen j)
    let p : ℕ → ℕ := bairePack (fun n => c (differenceLevelSequence i hi hic n))
    have hStage (j : Set.Iio i) :
        verticalSection (baireUniversalDifferenceFamily b i hi hic j) p = A j := by
      ext x
      constructor
      · intro hx
        obtain ⟨n, hnj, hxn⟩ :=
          mem_verticalSection_baireUniversalDifferenceFamily.1 hx
        have hxc : x ∈ verticalSection (baireParameterUniversalOpen b)
            (c (differenceLevelSequence i hi hic n)) := by
          simpa [p] using hxn
        rw [hc] at hxc
        exact hA hnj hxc
      · intro hx
        obtain ⟨n, hn⟩ := surjective_differenceLevelSequence i hi hic j
        apply mem_verticalSection_baireUniversalDifferenceFamily.2
        refine ⟨n, ?_, ?_⟩
        · rw [hn]
        · have hxc : x ∈ verticalSection (baireParameterUniversalOpen b) (c j) := by
            rw [hc]
            exact hx
          simpa [p, hn] using hxc
    refine ⟨p, ?_⟩
    rw [verticalSection_baireUniversalDifference]
    simpa only [hStage] using hAs
  · rintro ⟨p, rfl⟩
    let f : X → (ℕ → ℕ) × X := fun x => (p, x)
    have hf : Continuous f := continuous_const.prodMk continuous_id
    have hpre := (hausdorffDifference_baireUniversalDifference
      (fun n => hb.isOpen (Set.mem_range_self n)) hi hic).preimage hf
    change HausdorffDifference i (f ⁻¹' baireUniversalDifference b i hi hic)
    exact hpre

/-! ## Cantor parameters -/

/-- The open relation coded by component `n` of a Cantor parameter.-/
def cantorDifferenceOpenComponent {X : Type u} (b : ℕ → Set X) (n : ℕ) :
    Set ((ℕ → Bool) × X) :=
  (fun q => (cantorUnpack q.1 n, q.2)) ⁻¹' universalOpen b

/--
@isnad1 id=isopen.1h3v.s5.5b5acd572574 from=translated src=- shape=92c1ed9e vocab=846ec4ce
-/
theorem isOpen_cantorDifferenceOpenComponent {X : Type u}
    [TopologicalSpace X] {b : ℕ → Set X} (hb : ∀ n, IsOpen (b n)) (n : ℕ) :
    IsOpen (cantorDifferenceOpenComponent b n) := by
  exact (isOpen_universalOpen hb).preimage
    (((continuous_cantorUnpack n).comp continuous_fst).prodMk continuous_snd)

/-- The cumulative universal open family with Cantor parameters.-/
noncomputable def cantorUniversalDifferenceFamily {X : Type u}
    (b : ℕ → Set X) (i : Ordinal.{0}) (hi : 0 < i)
    (hic : IsCountableBorelLevel i) : Set.Iio i → Set ((ℕ → Bool) × X) := fun j =>
  ⋃ n, if (differenceLevelSequence i hi hic n).1 ≤ j.1 then
    cantorDifferenceOpenComponent b n else ∅

/--
@isnad1 id=iff.2h5v.s7.0fd0bfc21ff1 from=translated src=- shape=e626c000 vocab=1e88bbf7
-/
theorem mem_cantorUniversalDifferenceFamily {X : Type u}
    {b : ℕ → Set X} {i : Ordinal.{0}} {hi : 0 < i}
    {hic : IsCountableBorelLevel i} {j : Set.Iio i} {q : (ℕ → Bool) × X} :
    q ∈ cantorUniversalDifferenceFamily b i hi hic j ↔
      ∃ n, (differenceLevelSequence i hi hic n).1 ≤ j.1 ∧
        q ∈ cantorDifferenceOpenComponent b n := by
  simp [cantorUniversalDifferenceFamily]

/--
@isnad1 id=monotone.2h3v.s6.b1afde8511c2 from=translated src=- shape=b0bc309c vocab=48811190
-/
theorem monotone_cantorUniversalDifferenceFamily {X : Type u}
    (b : ℕ → Set X) (i : Ordinal.{0}) (hi : 0 < i)
    (hic : IsCountableBorelLevel i) :
    Monotone (cantorUniversalDifferenceFamily b i hi hic) := by
  intro j k hjk q hq
  obtain ⟨n, hnj, hqn⟩ := mem_cantorUniversalDifferenceFamily.1 hq
  exact mem_cantorUniversalDifferenceFamily.2 ⟨n, hnj.trans hjk, hqn⟩

/--
@isnad1 id=isopen.3h4v.s6.85261ab78bd6 from=translated src=- shape=53514d62 vocab=9dbd5385
-/
theorem isOpen_cantorUniversalDifferenceFamily {X : Type u}
    [TopologicalSpace X] {b : ℕ → Set X} (hb : ∀ n, IsOpen (b n))
    (i : Ordinal.{0}) (hi : 0 < i) (hic : IsCountableBorelLevel i)
    (j : Set.Iio i) : IsOpen (cantorUniversalDifferenceFamily b i hi hic j) := by
  apply isOpen_iUnion
  intro n
  split_ifs
  · exact isOpen_cantorDifferenceOpenComponent hb n
  · exact isOpen_empty

/-- The Cantor-parameter universal relation for exact Hausdorff differences.-/
noncomputable def cantorUniversalDifference {X : Type u} (b : ℕ → Set X)
    (i : Ordinal.{0}) (hi : 0 < i) (hic : IsCountableBorelLevel i) :
    Set ((ℕ → Bool) × X) :=
  difference i (cantorUniversalDifferenceFamily b i hi hic)

/--
@isnad1 id=hausdorf.3h3v.s6.435d9ed6a44b from=translated src=- shape=c4b6e64a vocab=32be3d77
-/
theorem hausdorffDifference_cantorUniversalDifference {X : Type u}
    [TopologicalSpace X] {b : ℕ → Set X} (hb : ∀ n, IsOpen (b n))
    {i : Ordinal.{0}} (hi : 0 < i) (hic : IsCountableBorelLevel i) :
    HausdorffDifference i (cantorUniversalDifference b i hi hic) := by
  exact ⟨hi, hic, cantorUniversalDifferenceFamily b i hi hic,
    monotone_cantorUniversalDifferenceFamily b i hi hic,
    isOpen_cantorUniversalDifferenceFamily hb i hi hic, rfl⟩

/--
@isnad1 id=iff.2h6v.s7.e62139e7222b from=translated src=- shape=ac2b701a vocab=196ca4a3
-/
theorem mem_verticalSection_cantorUniversalDifferenceFamily {X : Type u}
    {b : ℕ → Set X} {i : Ordinal.{0}} {hi : 0 < i}
    {hic : IsCountableBorelLevel i} {j : Set.Iio i} {p : ℕ → Bool} {x : X} :
    x ∈ verticalSection (cantorUniversalDifferenceFamily b i hi hic j) p ↔
      ∃ n, (differenceLevelSequence i hi hic n).1 ≤ j.1 ∧
        x ∈ verticalSection (universalOpen b) (cantorUnpack p n) := by
  simp [verticalSection, cantorDifferenceOpenComponent,
    cantorUniversalDifferenceFamily]

/--
@isnad1 id=eq.2h4v.s6.a1c78446e011 from=translated src=- shape=3baf4d49 vocab=d8d85205
-/
theorem verticalSection_cantorUniversalDifference {X : Type u}
    {b : ℕ → Set X} {i : Ordinal.{0}} {hi : 0 < i}
    {hic : IsCountableBorelLevel i} (p : ℕ → Bool) :
    verticalSection (cantorUniversalDifference b i hi hic) p =
      difference i (fun j =>
        verticalSection (cantorUniversalDifferenceFamily b i hi hic j) p) := by
  have hpre := preimage_difference (fun x : X => (p, x)) i
    (cantorUniversalDifferenceFamily b i hi hic)
  ext x
  change x ∈ (fun y : X => (p, y)) ⁻¹'
      difference i (cantorUniversalDifferenceFamily b i hi hic) ↔
    x ∈ difference i (fun j => (fun y : X => (p, y)) ⁻¹'
      cantorUniversalDifferenceFamily b i hi hic j)
  exact Set.ext_iff.mp hpre x

/-- The Cantor-parameter relation is universal for the exact level `i`.
@isnad1 id=isuniver.3h3v.s5.f72024e701e8 from=translated src=- shape=a4de14ab vocab=453d2661
-/
theorem isUniversalFor_cantorUniversalDifference {X : Type u}
    [TopologicalSpace X] {b : ℕ → Set X}
    (hb : IsTopologicalBasis (Set.range b)) {i : Ordinal.{0}}
    (hi : 0 < i) (hic : IsCountableBorelLevel i) :
    IsUniversalFor (HausdorffDifference i)
      (cantorUniversalDifference b i hi hic) := by
  intro s
  constructor
  · intro hs
    obtain ⟨_, _, A, hA, hAOpen, hAs⟩ := hs
    have hUniversal := (isUniversalOpen_universalOpen hb).2
    choose c hc using fun j => (hUniversal (A j)).1 (hAOpen j)
    let p : ℕ → Bool := cantorPack (fun n => c (differenceLevelSequence i hi hic n))
    have hStage (j : Set.Iio i) :
        verticalSection (cantorUniversalDifferenceFamily b i hi hic j) p = A j := by
      ext x
      constructor
      · intro hx
        obtain ⟨n, hnj, hxn⟩ :=
          mem_verticalSection_cantorUniversalDifferenceFamily.1 hx
        have hxc : x ∈ verticalSection (universalOpen b)
            (c (differenceLevelSequence i hi hic n)) := by
          simpa [p] using hxn
        rw [hc] at hxc
        exact hA hnj hxc
      · intro hx
        obtain ⟨n, hn⟩ := surjective_differenceLevelSequence i hi hic j
        apply mem_verticalSection_cantorUniversalDifferenceFamily.2
        refine ⟨n, ?_, ?_⟩
        · rw [hn]
        · have hxc : x ∈ verticalSection (universalOpen b) (c j) := by
            rw [hc]
            exact hx
          simpa [p, hn] using hxc
    refine ⟨p, ?_⟩
    rw [verticalSection_cantorUniversalDifference]
    simpa only [hStage] using hAs
  · rintro ⟨p, rfl⟩
    let f : X → (ℕ → Bool) × X := fun x => (p, x)
    have hf : Continuous f := continuous_const.prodMk continuous_id
    have hpre := (hausdorffDifference_cantorUniversalDifference
      (fun n => hb.isOpen (Set.mem_range_self n)) hi hic).preimage hf
    change HausdorffDifference i (f ⁻¹' cantorUniversalDifference b i hi hic)
    exact hpre

end DescriptiveSetTheory
