/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Borel.Code
import Tengoku.Seed.Data.Nat.Pairing
import Tengoku.Seed.Topology.GDelta.MetrizableSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The finite Borel hierarchy

This file defines the additive, multiplicative, and ambiguous finite Borel classes. The indexing
convention is deliberately one-based:

* level `0` is empty and reserved;
* `Sigma0 1` consists of the open sets and `Pi0 1` of the closed sets;
* `Sigma0 (n + 2)` consists of countable unions of `Pi0 (n + 1)` sets;
* `Pi0 (n + 2)` consists of countable intersections of `Sigma0 (n + 1)` sets.

Thus `Sigma0 2` is the class of F-sigma sets, while `Pi0 2` agrees with mathlib's `IsGδ`.
Complementation, continuous preimages, the defining countable operations, and finite Boolean
operations preserve the expected classes.

The hierarchy need not be nested for an arbitrary topological space: an open set need not be
F-sigma. Monotonicity is therefore stated under `PerfectlyNormalSpace`, an assumption automatically
available for pseudometrizable spaces.
-/

open MeasurableSpace Set

universe u v

namespace DescriptiveSetTheory

variable {X : Type u} [TopologicalSpace X]

private def finiteBorelClasses (X : Type u) [TopologicalSpace X] :
    ℕ → Set (Set X) × Set (Set X)
  | 0 => (∅, ∅)
  | 1 => ({s | IsOpen s}, {s | IsClosed s})
  | n + 2 =>
      ({s | ∃ f : ℕ → Set X,
          (∀ i, f i ∈ (finiteBorelClasses X (n + 1)).2) ∧ s = ⋃ i, f i},
       {s | ∃ f : ℕ → Set X,
          (∀ i, f i ∈ (finiteBorelClasses X (n + 1)).1) ∧ s = ⋂ i, f i})

/-- The additive Borel class at finite level `n`, using the one-based convention described above.-/
def Sigma0 (n : ℕ) (s : Set X) : Prop := s ∈ (finiteBorelClasses X n).1

/-- The multiplicative Borel class at finite level `n`, using the one-based convention.-/
def Pi0 (n : ℕ) (s : Set X) : Prop := s ∈ (finiteBorelClasses X n).2

/-- The ambiguous Borel class at level `n`: sets belonging to both polarities at that level.-/
def Delta0 (n : ℕ) (s : Set X) : Prop := Sigma0 n s ∧ Pi0 n s

/-- The reserved additive level zero contains no sets.
@isnad1 id=not.0h2v.s4.a6f7637112f8 from=translated src=- shape=76e0b577 vocab=2131535c
-/
@[simp] theorem sigma0_zero (s : Set X) : ¬ Sigma0 0 s := by
  simp [Sigma0, finiteBorelClasses]

/-- The reserved multiplicative level zero contains no sets.
@isnad1 id=not.0h2v.s4.5e58e7720e61 from=translated src=- shape=76e0b577 vocab=b077aaab
-/
@[simp] theorem pi0_zero (s : Set X) : ¬ Pi0 0 s := by
  simp [Pi0, finiteBorelClasses]

/-- The first additive class is exactly the class of open sets.
@isnad1 id=iff.0h2v.s4.6c97c802f378 from=translated src=- shape=50910fc0 vocab=125d4887
-/
@[simp] theorem sigma0_one_iff {s : Set X} : Sigma0 1 s ↔ IsOpen s := by
  rfl

/-- The first multiplicative class is exactly the class of closed sets.
@isnad1 id=iff.0h2v.s4.2abe0db2ce96 from=translated src=- shape=50910fc0 vocab=c96a8086
-/
@[simp] theorem pi0_one_iff {s : Set X} : Pi0 1 s ↔ IsClosed s := by
  rfl

/-- The defining countable-union characterization of a successor additive class.
@isnad1 id=iff.0h3v.s6.2976799726fa from=translated src=- shape=fdd8715e vocab=1e31a10d
-/
theorem sigma0_succ_succ {n : ℕ} {s : Set X} :
    Sigma0 (n + 2) s ↔ ∃ f : ℕ → Set X, (∀ i, Pi0 (n + 1) (f i)) ∧ s = ⋃ i, f i := by
  rfl

/-- The defining countable-intersection characterization of a successor multiplicative class.
@isnad1 id=iff.0h3v.s6.c2f8b57e3a6d from=translated src=- shape=fdd8715e vocab=9250f482
-/
theorem pi0_succ_succ {n : ℕ} {s : Set X} :
    Pi0 (n + 2) s ↔ ∃ f : ℕ → Set X, (∀ i, Sigma0 (n + 1) (f i)) ∧ s = ⋂ i, f i := by
  rfl

/-- Complementation exchanges additive and multiplicative classes at every finite level.
@isnad1 id=iff.0h3v.s4.0fba188f2497 from=translated src=- shape=54fffa35 vocab=23d2dd01
-/
theorem sigma0_compl_iff_pi0 (n : ℕ) (s : Set X) : Sigma0 n sᶜ ↔ Pi0 n s := by
  induction n using Nat.twoStepInduction generalizing s with
  | zero => simp
  | one => simp
  | more n _ ih =>
      rw [sigma0_succ_succ, pi0_succ_succ]
      constructor
      · rintro ⟨f, hf, hsf⟩
        refine ⟨fun i => (f i)ᶜ, fun i => (ih (f i)).2 (hf i), ?_⟩
        simpa using congrArg (fun t : Set X => tᶜ) hsf
      · rintro ⟨f, hf, hsf⟩
        refine ⟨fun i => (f i)ᶜ, ?_, ?_⟩
        · intro i
          have h := (ih ((f i)ᶜ)).1
          simpa using h (by simpa using hf i)
        · simpa using congrArg (fun t : Set X => tᶜ) hsf

/-- The dual formulation of `sigma0_compl_iff_pi0`.
@isnad1 id=iff.0h3v.s4.a67a2afe3f6f from=translated src=- shape=54fffa35 vocab=23d2dd01
-/
theorem pi0_compl_iff_sigma0 (n : ℕ) (s : Set X) : Pi0 n sᶜ ↔ Sigma0 n s := by
  simpa using (sigma0_compl_iff_pi0 n sᶜ).symm

/-- The complement of an additive-class set belongs to the corresponding multiplicative class.
@isnad1 id=pi0.1h3v.s4.3f574067a7b3 from=translated src=- shape=401cec24 vocab=23d2dd01
-/
theorem Sigma0.compl {n : ℕ} {s : Set X} (hs : Sigma0 n s) : Pi0 n sᶜ :=
  (pi0_compl_iff_sigma0 n s).2 hs

/-- The complement of a multiplicative-class set belongs to the corresponding additive class.
@isnad1 id=sigma0.1h3v.s4.d2deb2d8d8d9 from=translated src=- shape=401cec24 vocab=23d2dd01
-/
theorem Pi0.compl {n : ℕ} {s : Set X} (hs : Pi0 n s) : Sigma0 n sᶜ :=
  (sigma0_compl_iff_pi0 n s).2 hs

/-- Every open set belongs to the first additive class.
@isnad1 id=sigma0.1h2v.s4.55189d5e0ab0 from=translated src=- shape=0a2c2472 vocab=125d4887
-/
theorem sigma0_one_of_isOpen {s : Set X} (hs : IsOpen s) : Sigma0 1 s :=
  sigma0_one_iff.2 hs

/-- Every closed set belongs to the first multiplicative class.
@isnad1 id=pi0.1h2v.s4.130f1ff87cfa from=translated src=- shape=0a2c2472 vocab=c96a8086
-/
theorem pi0_one_of_isClosed {s : Set X} (hs : IsClosed s) : Pi0 1 s :=
  pi0_one_iff.2 hs

/-- Every closed set is F-sigma, represented by a constant sequence.
@isnad1 id=sigma0.1h2v.s4.835ae2adab42 from=translated src=- shape=0a2c2472 vocab=9821c556
-/
theorem sigma0_two_of_isClosed {s : Set X} (hs : IsClosed s) : Sigma0 2 s := by
  refine sigma0_succ_succ.2 ⟨fun _ => s, fun _ => pi0_one_of_isClosed hs, ?_⟩
  ext x
  simp

/-- A set is in `Sigma0 2` exactly when it is a countable union of closed sets.
@isnad1 id=iff.0h2v.s5.14260c7f005a from=translated src=- shape=f1ca0299 vocab=d9eb0cec
-/
theorem sigma0_two_iff_eq_iUnion_isClosed {s : Set X} :
    Sigma0 2 s ↔ ∃ f : ℕ → Set X, (∀ i, IsClosed (f i)) ∧ s = ⋃ i, f i := by
  simpa using (sigma0_succ_succ (X := X) (n := 0) (s := s))

/-- The second multiplicative class agrees with mathlib's predicate for G-delta sets.
@isnad1 id=iff.0h2v.s4.69c1035a9441 from=translated src=- shape=50910fc0 vocab=a22295fd
-/
theorem pi0_two_iff_isGδ {s : Set X} : Pi0 2 s ↔ IsGδ s :=
  pi0_succ_succ.trans isGδ_iff_eq_iInter_nat.symm

/-- A set is F-sigma exactly when its complement is G-delta.
@isnad1 id=iff.0h2v.s4.3e6f8c0dc99c from=translated src=- shape=2cf364da vocab=2a3298a8
-/
theorem sigma0_two_iff_isGδ_compl {s : Set X} : Sigma0 2 s ↔ IsGδ sᶜ :=
  (pi0_compl_iff_sigma0 2 s).symm.trans pi0_two_iff_isGδ

/-- The first ambiguous class consists of the clopen sets.
@isnad1 id=iff.0h2v.s4.cd4aae9ac9c6 from=translated src=- shape=9ae66f3f vocab=be6078c8
-/
@[simp] theorem delta0_one {s : Set X} : Delta0 1 s ↔ IsOpen s ∧ IsClosed s := by
  rfl

/-- Every finite-level additive-class set is Borel measurable.
@isnad1 id=measurab.1h3v.s4.094bd64252df from=translated src=- shape=18f26785 vocab=b04cc8ba
-/
theorem Sigma0.measurableSet {n : ℕ} {s : Set X} (hs : Sigma0 n s) :
    @MeasurableSet X (borel X) s := by
  induction n using Nat.twoStepInduction generalizing s with
  | zero => exact (sigma0_zero s hs).elim
  | one =>
      change GenerateMeasurable {t : Set X | IsOpen t} s
      exact .basic s (sigma0_one_iff.1 hs)
  | more n _ ih =>
      obtain ⟨f, hf, rfl⟩ := sigma0_succ_succ.1 hs
      exact MeasurableSet.iUnion fun i => by
        have hc : Sigma0 (n + 1) (f i)ᶜ :=
          (sigma0_compl_iff_pi0 (n + 1) (f i)).2 (hf i)
        simpa using (ih hc).compl

/-- Every finite-level multiplicative-class set is Borel measurable.
@isnad1 id=measurab.1h3v.s4.90bd755e7611 from=translated src=- shape=18f26785 vocab=9a03880f
-/
theorem Pi0.measurableSet {n : ℕ} {s : Set X} (hs : Pi0 n s) :
    @MeasurableSet X (borel X) s := by
  simpa using hs.compl.measurableSet.compl

/-- Every finite-level ambiguous-class set is Borel measurable.
@isnad1 id=measurab.1h3v.s4.d3b0b0fd519b from=translated src=- shape=18f26785 vocab=89757bad
-/
theorem Delta0.measurableSet {n : ℕ} {s : Set X} (hs : Delta0 n s) :
    @MeasurableSet X (borel X) s :=
  hs.1.measurableSet

/-- Continuous preimages preserve every finite additive Borel class.
@isnad1 id=sigma0.2h5v.s5.39d6e1fe49c9 from=translated src=- shape=c3ef64bf vocab=eb1b3512
-/
theorem Sigma0.preimage {Y : Type v} [TopologicalSpace Y] {n : ℕ} {s : Set Y}
    (hs : Sigma0 n s) {f : X → Y} (hf : Continuous f) : Sigma0 n (f ⁻¹' s) := by
  induction n using Nat.twoStepInduction generalizing s with
  | zero => exact (sigma0_zero s hs).elim
  | one => exact sigma0_one_iff.2 ((sigma0_one_iff.1 hs).preimage hf)
  | more n _ ih =>
      obtain ⟨g, hg, rfl⟩ := sigma0_succ_succ.1 hs
      refine sigma0_succ_succ.2 ⟨fun i => f ⁻¹' g i, ?_, preimage_iUnion⟩
      intro i
      have hc : Sigma0 (n + 1) (g i)ᶜ :=
        (sigma0_compl_iff_pi0 (n + 1) (g i)).2 (hg i)
      have hp : Sigma0 (n + 1) (f ⁻¹' (g i)ᶜ) := ih hc
      rw [preimage_compl] at hp
      exact (sigma0_compl_iff_pi0 (n + 1) (f ⁻¹' g i)).1 hp

/-- Continuous preimages preserve every finite multiplicative Borel class.
@isnad1 id=pi0.2h5v.s5.52c9d3536cf2 from=translated src=- shape=c3ef64bf vocab=9fca4bef
-/
theorem Pi0.preimage {Y : Type v} [TopologicalSpace Y] {n : ℕ} {s : Set Y}
    (hs : Pi0 n s) {f : X → Y} (hf : Continuous f) : Pi0 n (f ⁻¹' s) := by
  have h := hs.compl.preimage hf
  rw [preimage_compl] at h
  exact (sigma0_compl_iff_pi0 n (f ⁻¹' s)).1 h

/-- Continuous preimages preserve every finite ambiguous Borel class.
@isnad1 id=delta0.2h5v.s5.5a580b5ca506 from=translated src=- shape=c3ef64bf vocab=537bf0de
-/
theorem Delta0.preimage {Y : Type v} [TopologicalSpace Y] {n : ℕ} {s : Set Y}
    (hs : Delta0 n s) {f : X → Y} (hf : Continuous f) : Delta0 n (f ⁻¹' s) :=
  ⟨hs.1.preimage hf, hs.2.preimage hf⟩

/-- A countable union of additive-class sets at one level remains in that class.
@isnad1 id=sigma0.1h3v.s5.4cc6d6f9b4a1 from=translated src=- shape=a39a49cc vocab=8b181d28
-/
theorem Sigma0.iUnion {n : ℕ} {s : ℕ → Set X} (hs : ∀ i, Sigma0 n (s i)) :
    Sigma0 n (⋃ i, s i) := by
  induction n using Nat.twoStepInduction with
  | zero => exact (sigma0_zero (s 0) (hs 0)).elim
  | one => exact sigma0_one_iff.2 (isOpen_iUnion fun i => sigma0_one_iff.1 (hs i))
  | more n _ _ =>
      choose f hf hsf using fun i => sigma0_succ_succ.1 (hs i)
      refine sigma0_succ_succ.2
        ⟨fun k => f k.unpair.1 k.unpair.2, fun k => hf k.unpair.1 k.unpair.2, ?_⟩
      rw [Set.iUnion_unpair]
      simp_rw [hsf]

/-- A countable intersection of multiplicative-class sets at one level remains in that class.
@isnad1 id=pi0.1h3v.s5.ad8386dfa192 from=translated src=- shape=a39a49cc vocab=3be6ee06
-/
theorem Pi0.iInter {n : ℕ} {s : ℕ → Set X} (hs : ∀ i, Pi0 n (s i)) :
    Pi0 n (⋂ i, s i) := by
  have h := Sigma0.iUnion fun i => (hs i).compl
  simpa using h.compl

/-- Each finite additive class is closed under binary unions.
@isnad1 id=sigma0.2h4v.s5.fb0458d4eb8d from=translated src=- shape=ffb9e2f3 vocab=ab376f83
-/
theorem Sigma0.union {n : ℕ} {s t : Set X} (hs : Sigma0 n s) (ht : Sigma0 n t) :
    Sigma0 n (s ∪ t) := by
  have h : Sigma0 n (⋃ i : ℕ, if i = 0 then s else t) := Sigma0.iUnion fun i => by
    split_ifs
    · exact hs
    · exact ht
  convert h using 1
  ext x
  simp only [mem_union, mem_iUnion]
  constructor
  · rintro (hx | hx)
    · exact ⟨0, by simpa⟩
    · exact ⟨1, by simpa⟩
  · rintro ⟨i, hi⟩
    by_cases h0 : i = 0
    · exact Or.inl (by simpa [h0] using hi)
    · exact Or.inr (by simpa [h0] using hi)

/-- Each finite multiplicative class is closed under binary intersections.
@isnad1 id=pi0.2h4v.s5.c0a1a65a3bd7 from=translated src=- shape=ffb9e2f3 vocab=7239f40c
-/
theorem Pi0.inter {n : ℕ} {s t : Set X} (hs : Pi0 n s) (ht : Pi0 n t) :
    Pi0 n (s ∩ t) := by
  have h : Pi0 n (⋂ i : ℕ, if i = 0 then s else t) := Pi0.iInter fun i => by
    split_ifs
    · exact hs
    · exact ht
  convert h using 1
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · rintro ⟨hsx, htx⟩ i
    by_cases h0 : i = 0
    · simpa [h0]
    · simpa [h0]
  · intro hx
    exact ⟨by simpa using hx 0, by simpa using hx 1⟩

/-- Each finite additive class is closed under binary intersections.
@isnad1 id=sigma0.2h4v.s5.b0a8a71d0b44 from=translated src=- shape=ffb9e2f3 vocab=0f434b0b
-/
theorem Sigma0.inter {n : ℕ} {s t : Set X} (hs : Sigma0 n s) (ht : Sigma0 n t) :
    Sigma0 n (s ∩ t) := by
  induction n using Nat.twoStepInduction generalizing s t with
  | zero => exact (sigma0_zero s hs).elim
  | one => exact sigma0_one_iff.2 ((sigma0_one_iff.1 hs).inter (sigma0_one_iff.1 ht))
  | more n _ _ =>
      obtain ⟨f, hf, rfl⟩ := sigma0_succ_succ.1 hs
      obtain ⟨g, hg, rfl⟩ := sigma0_succ_succ.1 ht
      refine sigma0_succ_succ.2
        ⟨fun k => f k.unpair.1 ∩ g k.unpair.2,
          fun k => (hf k.unpair.1).inter (hg k.unpair.2), ?_⟩
      symm
      change (⋃ k : ℕ, f (Nat.unpair k).1 ∩ g (Nat.unpair k).2) = _
      rw [Set.iUnion_unpair (fun i j => f i ∩ g j)]
      ext x
      simp only [mem_iUnion, mem_inter_iff]
      constructor
      · rintro ⟨i, j, hfi, hgj⟩
        exact ⟨⟨i, hfi⟩, ⟨j, hgj⟩⟩
      · rintro ⟨⟨i, hfi⟩, ⟨j, hgj⟩⟩
        exact ⟨i, j, hfi, hgj⟩

/-- Each finite multiplicative class is closed under binary unions.
@isnad1 id=pi0.2h4v.s5.39f84bee66a5 from=translated src=- shape=ffb9e2f3 vocab=221feeff
-/
theorem Pi0.union {n : ℕ} {s t : Set X} (hs : Pi0 n s) (ht : Pi0 n t) :
    Pi0 n (s ∪ t) := by
  rw [Set.union_eq_compl_compl_inter_compl]
  exact (hs.compl.inter ht.compl).compl

/-- Each finite ambiguous class is closed under binary unions.
@isnad1 id=delta0.2h4v.s5.a56599736076 from=translated src=- shape=ffb9e2f3 vocab=c23e0889
-/
theorem Delta0.union {n : ℕ} {s t : Set X} (hs : Delta0 n s) (ht : Delta0 n t) :
    Delta0 n (s ∪ t) :=
  ⟨hs.1.union ht.1, hs.2.union ht.2⟩

/-- Each finite ambiguous class is closed under binary intersections.
@isnad1 id=delta0.2h4v.s5.f37fa45a4c0c from=translated src=- shape=ffb9e2f3 vocab=4e172542
-/
theorem Delta0.inter {n : ℕ} {s t : Set X} (hs : Delta0 n s) (ht : Delta0 n t) :
    Delta0 n (s ∩ t) :=
  ⟨hs.1.inter ht.1, hs.2.inter ht.2⟩

private theorem sigma0_empty_univ (n : ℕ) :
    Sigma0 (n + 1) (∅ : Set X) ∧ Sigma0 (n + 1) (Set.univ : Set X) := by
  induction n with
  | zero => simp
  | succ n ih =>
      constructor
      · refine sigma0_succ_succ.2 ⟨fun _ => ∅, ?_, ?_⟩
        · intro i
          simpa using ih.2.compl
        · ext x
          simp
      · refine sigma0_succ_succ.2 ⟨fun _ => Set.univ, ?_, ?_⟩
        · intro i
          simpa using ih.1.compl
        · ext x
          simp

/-- The empty set belongs to every positive finite additive class.
@isnad1 id=sigma0.1h2v.s4.3b8a9859c3ec from=translated src=- shape=39e1edc0 vocab=2096e6ee
-/
theorem sigma0_empty {n : ℕ} (hn : 0 < n) : Sigma0 n (∅ : Set X) := by
  cases n with
  | zero => simp at hn
  | succ n => simpa [Nat.succ_eq_add_one] using (sigma0_empty_univ (X := X) n).1

/-- The universal set belongs to every positive finite additive class.
@isnad1 id=sigma0.1h2v.s4.20476e81900f from=translated src=- shape=68876593 vocab=66b533a5
-/
theorem sigma0_univ {n : ℕ} (hn : 0 < n) : Sigma0 n (Set.univ : Set X) := by
  cases n with
  | zero => simp at hn
  | succ n => simpa [Nat.succ_eq_add_one] using (sigma0_empty_univ (X := X) n).2

/-- The empty set belongs to every positive finite multiplicative class.
@isnad1 id=pi0.1h2v.s4.b51850bf75b6 from=translated src=- shape=39e1edc0 vocab=4010851e
-/
theorem pi0_empty {n : ℕ} (hn : 0 < n) : Pi0 n (∅ : Set X) := by
  simpa using (sigma0_univ (X := X) hn).compl

/-- The universal set belongs to every positive finite multiplicative class.
@isnad1 id=pi0.1h2v.s4.21810e02510b from=translated src=- shape=68876593 vocab=1267d8ef
-/
theorem pi0_univ {n : ℕ} (hn : 0 < n) : Pi0 n (Set.univ : Set X) := by
  simpa using (sigma0_empty (X := X) hn).compl

/-- The empty set belongs to every positive finite ambiguous class.
@isnad1 id=delta0.1h2v.s4.4dab32ee1c82 from=translated src=- shape=39e1edc0 vocab=fabd6d8d
-/
theorem delta0_empty {n : ℕ} (hn : 0 < n) : Delta0 n (∅ : Set X) :=
  ⟨sigma0_empty hn, pi0_empty hn⟩

/-- The universal set belongs to every positive finite ambiguous class.
@isnad1 id=delta0.1h2v.s4.400653208d9b from=translated src=- shape=68876593 vocab=2ce46741
-/
theorem delta0_univ {n : ℕ} (hn : 0 < n) : Delta0 n (Set.univ : Set X) :=
  ⟨sigma0_univ hn, pi0_univ hn⟩

/-- A finite union of sets in one positive additive class remains in that class.
@isnad1 id=sigma0.2h5v.s6.52d47e294f98 from=translated src=- shape=f46c60c3 vocab=6ad9a855
-/
theorem Sigma0.iUnion_finset {ι : Type*} {n : ℕ} (hn : 0 < n) (I : Finset ι)
    {s : ι → Set X} (hs : ∀ i ∈ I, Sigma0 n (s i)) : Sigma0 n (⋃ i ∈ I, s i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using sigma0_empty (X := X) hn
  | @insert a I ha ih =>
      rw [Finset.set_biUnion_insert]
      exact (hs a (Finset.mem_insert_self a I)).union
        (ih fun i hi => hs i (Finset.mem_insert_of_mem hi))

/-- A finite intersection of sets in one positive additive class remains in that class.
@isnad1 id=sigma0.2h5v.s6.a7251f49fbab from=translated src=- shape=f46c60c3 vocab=2a45e4fb
-/
theorem Sigma0.iInter_finset {ι : Type*} {n : ℕ} (hn : 0 < n) (I : Finset ι)
    {s : ι → Set X} (hs : ∀ i ∈ I, Sigma0 n (s i)) : Sigma0 n (⋂ i ∈ I, s i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using sigma0_univ (X := X) hn
  | @insert a I ha ih =>
      rw [Finset.set_biInter_insert]
      exact (hs a (Finset.mem_insert_self a I)).inter
        (ih fun i hi => hs i (Finset.mem_insert_of_mem hi))

/-- A finite union of sets in one positive multiplicative class remains in that class.
@isnad1 id=pi0.2h5v.s6.bad8dffa88d8 from=translated src=- shape=f46c60c3 vocab=99a11104
-/
theorem Pi0.iUnion_finset {ι : Type*} {n : ℕ} (hn : 0 < n) (I : Finset ι)
    {s : ι → Set X} (hs : ∀ i ∈ I, Pi0 n (s i)) : Pi0 n (⋃ i ∈ I, s i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using pi0_empty (X := X) hn
  | @insert a I ha ih =>
      rw [Finset.set_biUnion_insert]
      exact (hs a (Finset.mem_insert_self a I)).union
        (ih fun i hi => hs i (Finset.mem_insert_of_mem hi))

/-- A finite intersection of sets in one positive multiplicative class remains in that class.
@isnad1 id=pi0.2h5v.s6.2dc67fab35f0 from=translated src=- shape=f46c60c3 vocab=ce3b048b
-/
theorem Pi0.iInter_finset {ι : Type*} {n : ℕ} (hn : 0 < n) (I : Finset ι)
    {s : ι → Set X} (hs : ∀ i ∈ I, Pi0 n (s i)) : Pi0 n (⋂ i ∈ I, s i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using pi0_univ (X := X) hn
  | @insert a I ha ih =>
      rw [Finset.set_biInter_insert]
      exact (hs a (Finset.mem_insert_self a I)).inter
        (ih fun i hi => hs i (Finset.mem_insert_of_mem hi))

/-- A finite union of sets in one positive ambiguous class remains in that class.
@isnad1 id=delta0.2h5v.s6.168c89d4864d from=translated src=- shape=f46c60c3 vocab=2566bd0e
-/
theorem Delta0.iUnion_finset {ι : Type*} {n : ℕ} (hn : 0 < n) (I : Finset ι)
    {s : ι → Set X} (hs : ∀ i ∈ I, Delta0 n (s i)) : Delta0 n (⋃ i ∈ I, s i) :=
  ⟨Sigma0.iUnion_finset hn I fun i hi => (hs i hi).1,
    Pi0.iUnion_finset hn I fun i hi => (hs i hi).2⟩

/-- A finite intersection of sets in one positive ambiguous class remains in that class.
@isnad1 id=delta0.2h5v.s6.5c08f2b14669 from=translated src=- shape=f46c60c3 vocab=f85468e0
-/
theorem Delta0.iInter_finset {ι : Type*} {n : ℕ} (hn : 0 < n) (I : Finset ι)
    {s : ι → Set X} (hs : ∀ i ∈ I, Delta0 n (s i)) : Delta0 n (⋂ i ∈ I, s i) :=
  ⟨Sigma0.iInter_finset hn I fun i hi => (hs i hi).1,
    Pi0.iInter_finset hn I fun i hi => (hs i hi).2⟩

/-- In a perfectly normal space, an additive class is contained in its successor class.
@isnad1 id=sigma0.1h3v.s5.9c8c0f1ebe93 from=translated src=- shape=e4143e15 vocab=afe10dfd
-/
theorem Sigma0.mono_succ [PerfectlyNormalSpace X] {n : ℕ} {s : Set X}
    (hs : Sigma0 (n + 1) s) : Sigma0 (n + 2) s := by
  induction n generalizing s with
  | zero =>
      exact sigma0_two_iff_isGδ_compl.2
        (isClosed_compl_iff.mpr (sigma0_one_iff.1 hs)).isGδ
  | succ n ih =>
      obtain ⟨f, hf, rfl⟩ := sigma0_succ_succ.1 hs
      refine sigma0_succ_succ.2 ⟨f, ?_, rfl⟩
      intro i
      simpa [Nat.succ_eq_add_one] using (ih (hf i).compl).compl

/-- In a perfectly normal space, a multiplicative class is contained in its successor class.
@isnad1 id=pi0.1h3v.s5.33ed0849c51f from=translated src=- shape=e4143e15 vocab=8c7dd4d7
-/
theorem Pi0.mono_succ [PerfectlyNormalSpace X] {n : ℕ} {s : Set X}
    (hs : Pi0 (n + 1) s) : Pi0 (n + 2) s := by
  simpa using hs.compl.mono_succ.compl

/-- In a perfectly normal space, an ambiguous class is contained in its successor class.
@isnad1 id=delta0.1h3v.s5.306bf8757fc9 from=translated src=- shape=e4143e15 vocab=3e806132
-/
theorem Delta0.mono_succ [PerfectlyNormalSpace X] {n : ℕ} {s : Set X}
    (hs : Delta0 (n + 1) s) : Delta0 (n + 2) s :=
  ⟨hs.1.mono_succ, hs.2.mono_succ⟩

/-- Additive finite Borel classes are monotone in perfectly normal spaces.
@isnad1 id=sigma0.2h4v.s5.ffeb154f9e7f from=translated src=- shape=328d8547 vocab=82444f69
-/
theorem Sigma0.mono [PerfectlyNormalSpace X] {m n : ℕ} (hmn : m ≤ n) {s : Set X}
    (hs : Sigma0 m s) : Sigma0 n s := by
  induction n, hmn using Nat.le_induction with
  | base => exact hs
  | succ n _ ih =>
      cases n with
      | zero => exact (sigma0_zero s ih).elim
      | succ n => simpa [Nat.succ_eq_add_one] using ih.mono_succ

/-- Multiplicative finite Borel classes are monotone in perfectly normal spaces.
@isnad1 id=pi0.2h4v.s5.3182fbcb9b9e from=translated src=- shape=328d8547 vocab=13567f05
-/
theorem Pi0.mono [PerfectlyNormalSpace X] {m n : ℕ} (hmn : m ≤ n) {s : Set X}
    (hs : Pi0 m s) : Pi0 n s := by
  simpa using hs.compl.mono hmn |>.compl

/-- Ambiguous finite Borel classes are monotone in perfectly normal spaces.
@isnad1 id=delta0.2h4v.s5.cf72a622ff92 from=translated src=- shape=328d8547 vocab=ad17db87
-/
theorem Delta0.mono [PerfectlyNormalSpace X] {m n : ℕ} (hmn : m ≤ n) {s : Set X}
    (hs : Delta0 m s) : Delta0 n s :=
  ⟨hs.1.mono hmn, hs.2.mono hmn⟩

/-- Every finite-level additive-class set is represented by a `BorelCode`.
@isnad1 id=ex.1h3v.s5.a0a21b197251 from=translated src=- shape=98dc3a72 vocab=e973aed1
-/
theorem Sigma0.exists_borelCode {n : ℕ} {s : Set X} (hs : Sigma0 n s) :
    ∃ c : BorelCode X, c.eval = s :=
  BorelCode.borelMeasurableSet_iff_exists_code.1 hs.measurableSet

/-- Every finite-level multiplicative-class set is represented by a `BorelCode`.
@isnad1 id=ex.1h3v.s5.d6ab9053056b from=translated src=- shape=98dc3a72 vocab=d2826c08
-/
theorem Pi0.exists_borelCode {n : ℕ} {s : Set X} (hs : Pi0 n s) :
    ∃ c : BorelCode X, c.eval = s :=
  BorelCode.borelMeasurableSet_iff_exists_code.1 hs.measurableSet

/-- Every finite-level ambiguous-class set is represented by a `BorelCode`.
@isnad1 id=ex.1h3v.s5.8c2e35d30c4d from=translated src=- shape=98dc3a72 vocab=da36dea9
-/
theorem Delta0.exists_borelCode {n : ℕ} {s : Set X} (hs : Delta0 n s) :
    ∃ c : BorelCode X, c.eval = s :=
  hs.1.exists_borelCode

end DescriptiveSetTheory
