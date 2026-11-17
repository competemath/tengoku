/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Borel.ConstructionRank
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Borel.FiniteHierarchy

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The ordinal-indexed Borel hierarchy

This file extends the finite hierarchy to ordinal indices. The intended Borel levels satisfy
`IsCountableBorelLevel i`, meaning `i < ω₁`; the recursive predicates are defined for all small
ordinals so that lower-level recursion remains direct.

The indexing convention agrees with `FiniteHierarchy`:

* level `0` is empty and reserved;
* `OrdinalSigma0 1` consists of open sets and `OrdinalPi0 1` of closed sets;
* at every other level `i`, the additive class consists of countable unions of multiplicative sets
  whose individual indices are strictly below `i`, and dually for the multiplicative class.

The final clause treats successor and limit levels uniformly. In particular, level `2` is exactly
F-sigma/G-delta. This module proves complement duality, Borel measurability, continuous-preimage
closure, and closure under the defining countable operations.

As in the finite hierarchy, monotonicity is deliberately not built into these definitions: it needs
an additional separation assumption because an open set need not be F-sigma in an arbitrary
topological space.
-/

open Cardinal Ordinal Set

universe u

namespace DescriptiveSetTheory

variable {X : Type u} [TopologicalSpace X]

/-- An ordinal is an intended Borel-hierarchy index when it is strictly below `ω₁`.-/
def IsCountableBorelLevel (i : Ordinal.{0}) : Prop := i < ω₁

/-- The initial segment below a countable Borel level is a countable type.
@isnad1 id=countabl.1h1v.s3.e4f63823d7b6 from=translated src=- shape=717ee240 vocab=6e69fc01
-/
theorem countable_Iio_of_isCountableBorelLevel {i : Ordinal.{0}}
    (hi : IsCountableBorelLevel i) : Countable (Set.Iio i) := by
  rw [← Cardinal.mk_le_aleph0_iff, Cardinal.mk_Iio_ordinal]
  have hcard : i.card < ℵ₁ := Cardinal.lt_omega_iff_card_lt.mp hi
  exact Cardinal.lift_le_aleph0.mpr (Cardinal.lt_aleph_one_iff.mp hcard)

/-- Every natural-number ordinal is a countable Borel level.
@isnad1 id=iscounta.0h1v.s3.6a9dcefd556b from=translated src=- shape=4c19b7a8 vocab=b751e703
-/
theorem isCountableBorelLevel_nat (n : ℕ) : IsCountableBorelLevel n :=
  (Ordinal.natCast_lt_omega0 n).trans Ordinal.omega0_lt_omega_one

private noncomputable def ordinalBorelClasses (X : Type u) [TopologicalSpace X]
    (i : Ordinal.{0}) : Set (Set X) × Set (Set X) :=
  if i = 0 then
    (∅, ∅)
  else if i = 1 then
    ({s | IsOpen s}, {s | IsClosed s})
  else
    ({s | ∃ f : ℕ → Set X, ∃ j : ℕ → Set.Iio i,
        (∀ n, f n ∈ (ordinalBorelClasses X (j n).1).2) ∧ s = ⋃ n, f n},
     {s | ∃ f : ℕ → Set X, ∃ j : ℕ → Set.Iio i,
        (∀ n, f n ∈ (ordinalBorelClasses X (j n).1).1) ∧ s = ⋂ n, f n})
termination_by i
decreasing_by
  all_goals
    exact (j n).property

/-- The additive Borel class at ordinal level `i`. Intended indices satisfy `i < ω₁`.-/
def OrdinalSigma0 (i : Ordinal.{0}) (s : Set X) : Prop :=
  s ∈ (ordinalBorelClasses X i).1

/-- The multiplicative Borel class at ordinal level `i`. Intended indices satisfy `i < ω₁`.-/
def OrdinalPi0 (i : Ordinal.{0}) (s : Set X) : Prop :=
  s ∈ (ordinalBorelClasses X i).2

/-- The ambiguous Borel class at ordinal level `i`.-/
def OrdinalDelta0 (i : Ordinal.{0}) (s : Set X) : Prop :=
  OrdinalSigma0 i s ∧ OrdinalPi0 i s

/-- The reserved ordinal-indexed additive level zero contains no sets.
@isnad1 id=not.0h2v.s4.d1818a558afa from=translated src=- shape=76e0b577 vocab=bec6b27b
-/
@[simp] theorem ordinalSigma0_zero (s : Set X) : ¬ OrdinalSigma0 0 s := by
  simp [OrdinalSigma0, ordinalBorelClasses]

/-- The reserved ordinal-indexed multiplicative level zero contains no sets.
@isnad1 id=not.0h2v.s4.483bed5f233b from=translated src=- shape=76e0b577 vocab=80463baf
-/
@[simp] theorem ordinalPi0_zero (s : Set X) : ¬ OrdinalPi0 0 s := by
  simp [OrdinalPi0, ordinalBorelClasses]

/-- The first ordinal-indexed additive class is exactly the class of open sets.
@isnad1 id=iff.0h2v.s4.0368fb4432d4 from=translated src=- shape=50910fc0 vocab=faff2f66
-/
@[simp] theorem ordinalSigma0_one_iff {s : Set X} : OrdinalSigma0 1 s ↔ IsOpen s := by
  simp [OrdinalSigma0, ordinalBorelClasses]

/-- The first ordinal-indexed multiplicative class is exactly the class of closed sets.
@isnad1 id=iff.0h2v.s4.22a58d4960ea from=translated src=- shape=50910fc0 vocab=44730aab
-/
@[simp] theorem ordinalPi0_one_iff {s : Set X} : OrdinalPi0 1 s ↔ IsClosed s := by
  simp [OrdinalPi0, ordinalBorelClasses]

/-- At every level other than zero and one, the additive class is formed from countably many
strictly lower multiplicative classes. This is the uniform successor/limit equation.
@isnad1 id=iff.2h3v.s6.0d432224a7d1 from=translated src=- shape=6b3d36ae vocab=36cd4859
-/
theorem ordinalSigma0_of_ne_zero_one {i : Ordinal.{0}} (hi0 : i ≠ 0) (hi1 : i ≠ 1)
    {s : Set X} :
    OrdinalSigma0 i s ↔ ∃ f : ℕ → Set X, ∃ j : ℕ → Set.Iio i,
      (∀ n, OrdinalPi0 (j n).1 (f n)) ∧ s = ⋃ n, f n := by
  change s ∈ (ordinalBorelClasses X i).1 ↔ ∃ f : ℕ → Set X, ∃ j : ℕ → Set.Iio i,
    (∀ n, f n ∈ (ordinalBorelClasses X (j n).1).2) ∧ s = ⋃ n, f n
  rw [ordinalBorelClasses.eq_1, ite_eq_right hi0, ite_eq_right hi1]
  rfl

/-- At every level other than zero and one, the multiplicative class is formed from countably many
strictly lower additive classes. This is the uniform successor/limit equation.
@isnad1 id=iff.2h3v.s6.0d44e806484a from=translated src=- shape=6b3d36ae vocab=174ff270
-/
theorem ordinalPi0_of_ne_zero_one {i : Ordinal.{0}} (hi0 : i ≠ 0) (hi1 : i ≠ 1)
    {s : Set X} :
    OrdinalPi0 i s ↔ ∃ f : ℕ → Set X, ∃ j : ℕ → Set.Iio i,
      (∀ n, OrdinalSigma0 (j n).1 (f n)) ∧ s = ⋂ n, f n := by
  change s ∈ (ordinalBorelClasses X i).2 ↔ ∃ f : ℕ → Set X, ∃ j : ℕ → Set.Iio i,
    (∀ n, f n ∈ (ordinalBorelClasses X (j n).1).1) ∧ s = ⋂ n, f n
  rw [ordinalBorelClasses.eq_1, ite_eq_right hi0, ite_eq_right hi1]
  rfl

/-- Every clopen set belongs to the multiplicative class at each positive ordinal level.
@isnad1 id=ordinalp.3h3v.s5.ccb65a0f41fe from=translated src=- shape=5f5f092c vocab=d4cca1cc
-/
theorem ordinalPi0_of_isClopen {i : Ordinal.{0}} {s : Set X} (hi : 0 < i)
    (hsOpen : IsOpen s) (hsClosed : IsClosed s) : OrdinalPi0 i s := by
  by_cases hi1 : i = 1
  · subst i
    exact ordinalPi0_one_iff.2 hsClosed
  · have h1i : (1 : Ordinal) < i :=
      lt_of_le_of_ne (Order.one_le_iff_ne_zero.mpr (ne_of_gt hi)) (Ne.symm hi1)
    refine (ordinalPi0_of_ne_zero_one (ne_of_gt hi) hi1).2
      ⟨fun _ => s, fun _ => ⟨1, h1i⟩, fun _ => ordinalSigma0_one_iff.2 hsOpen, ?_⟩
    ext x
    simp

/-- Complementation exchanges ordinal-indexed additive and multiplicative classes.
@isnad1 id=iff.0h3v.s4.ebbe8a481ec2 from=translated src=- shape=54fffa35 vocab=ebcbb338
-/
theorem ordinalSigma0_compl_iff_pi0 (i : Ordinal.{0}) (s : Set X) :
    OrdinalSigma0 i sᶜ ↔ OrdinalPi0 i s := by
  induction i using WellFoundedLT.induction generalizing s with
  | ind i ih =>
      by_cases hi0 : i = 0
      · subst i
        simp
      by_cases hi1 : i = 1
      · subst i
        simp
      rw [ordinalSigma0_of_ne_zero_one hi0 hi1, ordinalPi0_of_ne_zero_one hi0 hi1]
      constructor
      · rintro ⟨f, j, hf, hsf⟩
        refine ⟨fun n => (f n)ᶜ, j, fun n => (ih (j n).1 (j n).2 (f n)).2 (hf n), ?_⟩
        simpa using congrArg (fun t : Set X => tᶜ) hsf
      · rintro ⟨f, j, hf, hsf⟩
        refine ⟨fun n => (f n)ᶜ, j, ?_, ?_⟩
        · intro n
          have h := (ih (j n).1 (j n).2 ((f n)ᶜ)).1
          simpa using h (by simpa using hf n)
        · simpa using congrArg (fun t : Set X => tᶜ) hsf

/-- The dual formulation of `ordinalSigma0_compl_iff_pi0`.
@isnad1 id=iff.0h3v.s4.3ab9f04d8eba from=translated src=- shape=54fffa35 vocab=ebcbb338
-/
theorem ordinalPi0_compl_iff_sigma0 (i : Ordinal.{0}) (s : Set X) :
    OrdinalPi0 i sᶜ ↔ OrdinalSigma0 i s := by
  simpa using (ordinalSigma0_compl_iff_pi0 i sᶜ).symm

/-- The complement of an ordinal additive-class set belongs to the dual class.
@isnad1 id=ordinalp.1h3v.s4.520853875235 from=translated src=- shape=401cec24 vocab=ebcbb338
-/
theorem OrdinalSigma0.compl {i : Ordinal.{0}} {s : Set X} (hs : OrdinalSigma0 i s) :
    OrdinalPi0 i sᶜ :=
  (ordinalPi0_compl_iff_sigma0 i s).2 hs

/-- The complement of an ordinal multiplicative-class set belongs to the dual class.
@isnad1 id=ordinals.1h3v.s4.0d7d779e43d9 from=translated src=- shape=401cec24 vocab=ebcbb338
-/
theorem OrdinalPi0.compl {i : Ordinal.{0}} {s : Set X} (hs : OrdinalPi0 i s) :
    OrdinalSigma0 i sᶜ :=
  (ordinalSigma0_compl_iff_pi0 i s).2 hs

/-- Every clopen set belongs to the additive class at each positive ordinal level.
@isnad1 id=ordinals.3h3v.s5.6129d876fbc6 from=translated src=- shape=5f5f092c vocab=38c46c32
-/
theorem ordinalSigma0_of_isClopen {i : Ordinal.{0}} {s : Set X} (hi : 0 < i)
    (hsOpen : IsOpen s) (hsClosed : IsClosed s) : OrdinalSigma0 i s := by
  have hcompl : OrdinalPi0 i sᶜ :=
    ordinalPi0_of_isClopen hi hsClosed.isOpen_compl hsOpen.isClosed_compl
  simpa using hcompl.compl

/-- Every ordinal ambiguous class is closed under complementation.
@isnad1 id=ordinald.1h3v.s4.b19b434d31a7 from=translated src=- shape=1ffb9ab6 vocab=9a1336f5
-/
theorem OrdinalDelta0.compl {i : Ordinal.{0}} {s : Set X} (hs : OrdinalDelta0 i s) :
    OrdinalDelta0 i sᶜ :=
  ⟨hs.2.compl, hs.1.compl⟩

/-- The second ordinal additive class is exactly the class of countable unions of closed sets.
@isnad1 id=iff.0h2v.s5.e17774a025a5 from=translated src=- shape=5665ddd2 vocab=5ba76178
-/
theorem ordinalSigma0_two_iff_eq_iUnion_isClosed {s : Set X} :
    OrdinalSigma0 2 s ↔ ∃ f : ℕ → Set X, (∀ n, IsClosed (f n)) ∧ s = ⋃ n, f n := by
  rw [ordinalSigma0_of_ne_zero_one (by norm_num) (by norm_num)]
  constructor
  · rintro ⟨f, j, hf, hsf⟩
    refine ⟨f, ?_, hsf⟩
    intro n
    have hjlt : (j n).1 < (1 : Ordinal) + 1 := by
      rw [one_add_one_eq_two]
      exact (j n).property
    have hjle : (j n).1 ≤ (1 : Ordinal) := Order.lt_add_one_iff.mp hjlt
    rcases eq_or_lt_of_le hjle with h1 | h0
    · simpa [h1] using hf n
    · have hj0 : (j n).1 = 0 := Order.lt_one_iff.mp h0
      exact (ordinalPi0_zero (f n) (by simpa [hj0] using hf n)).elim
  · rintro ⟨f, hf, hsf⟩
    refine ⟨f, fun _ => ⟨1, by norm_num⟩, ?_, hsf⟩
    intro n
    simpa using hf n

/-- The ordinal and finite additive hierarchies agree at level two.
@isnad1 id=iff.0h2v.s5.1a06cbfaa632 from=translated src=- shape=13580020 vocab=5c2e942a
-/
theorem ordinalSigma0_two_iff_sigma0_two {s : Set X} : OrdinalSigma0 2 s ↔ Sigma0 2 s :=
  ordinalSigma0_two_iff_eq_iUnion_isClosed.trans sigma0_two_iff_eq_iUnion_isClosed.symm

/-- The ordinal and finite multiplicative hierarchies agree at level two.
@isnad1 id=iff.0h2v.s5.91b76396c46e from=translated src=- shape=13580020 vocab=1e18f699
-/
theorem ordinalPi0_two_iff_pi0_two {s : Set X} : OrdinalPi0 2 s ↔ Pi0 2 s := by
  calc
    OrdinalPi0 2 s ↔ OrdinalSigma0 2 sᶜ := (ordinalSigma0_compl_iff_pi0 2 s).symm
    _ ↔ Sigma0 2 sᶜ := ordinalSigma0_two_iff_sigma0_two
    _ ↔ Pi0 2 s := sigma0_compl_iff_pi0 2 s

/-- The second ordinal multiplicative class agrees with mathlib's G-delta predicate.
@isnad1 id=iff.0h2v.s4.b314c14b4612 from=translated src=- shape=50910fc0 vocab=62779b7c
-/
theorem ordinalPi0_two_iff_isGδ {s : Set X} : OrdinalPi0 2 s ↔ IsGδ s :=
  ordinalPi0_two_iff_pi0_two.trans pi0_two_iff_isGδ

/-- Every ordinal-indexed additive-class set is Borel measurable.
@isnad1 id=measurab.1h3v.s4.fe312ffa2db2 from=translated src=- shape=18f26785 vocab=f7d626ba
-/
theorem OrdinalSigma0.measurableSet {i : Ordinal.{0}} {s : Set X}
    (hs : OrdinalSigma0 i s) : @MeasurableSet X (borel X) s := by
  induction i using WellFoundedLT.induction generalizing s with
  | ind i ih =>
      by_cases hi0 : i = 0
      · subst i
        exact (ordinalSigma0_zero s hs).elim
      by_cases hi1 : i = 1
      · subst i
        exact MeasurableSpace.GenerateMeasurable.basic s (ordinalSigma0_one_iff.1 hs)
      obtain ⟨f, j, hf, rfl⟩ := (ordinalSigma0_of_ne_zero_one hi0 hi1).1 hs
      exact MeasurableSet.iUnion fun n => by
        have hc : OrdinalSigma0 (j n).1 (f n)ᶜ :=
          (ordinalSigma0_compl_iff_pi0 (j n).1 (f n)).2 (hf n)
        simpa using (ih (j n).1 (j n).2 hc).compl

/-- Every ordinal-indexed multiplicative-class set is Borel measurable.
@isnad1 id=measurab.1h3v.s4.45b68a0e72c3 from=translated src=- shape=18f26785 vocab=9154d82c
-/
theorem OrdinalPi0.measurableSet {i : Ordinal.{0}} {s : Set X} (hs : OrdinalPi0 i s) :
    @MeasurableSet X (borel X) s := by
  simpa using hs.compl.measurableSet.compl

/-- Every ordinal-indexed ambiguous-class set is Borel measurable.
@isnad1 id=measurab.1h3v.s4.a00430a4d18b from=translated src=- shape=18f26785 vocab=9cf1d6fd
-/
theorem OrdinalDelta0.measurableSet {i : Ordinal.{0}} {s : Set X}
    (hs : OrdinalDelta0 i s) : @MeasurableSet X (borel X) s :=
  hs.1.measurableSet

/-- Continuous preimages preserve every ordinal additive Borel class.
@isnad1 id=ordinals.2h5v.s5.502fb7e82cad from=translated src=- shape=c3ef64bf vocab=394fd27a
-/
theorem OrdinalSigma0.preimage {Y : Type*} [TopologicalSpace Y] {i : Ordinal.{0}}
    {s : Set Y} (hs : OrdinalSigma0 i s) {f : X → Y} (hf : Continuous f) :
    OrdinalSigma0 i (f ⁻¹' s) := by
  induction i using WellFoundedLT.induction generalizing s with
  | ind i ih =>
      by_cases hi0 : i = 0
      · subst i
        exact (ordinalSigma0_zero s hs).elim
      by_cases hi1 : i = 1
      · subst i
        exact ordinalSigma0_one_iff.2 ((ordinalSigma0_one_iff.1 hs).preimage hf)
      obtain ⟨g, j, hg, rfl⟩ := (ordinalSigma0_of_ne_zero_one hi0 hi1).1 hs
      refine (ordinalSigma0_of_ne_zero_one hi0 hi1).2
        ⟨fun n => f ⁻¹' g n, j, ?_, preimage_iUnion⟩
      intro n
      have hc : OrdinalSigma0 (j n).1 (g n)ᶜ :=
        (ordinalSigma0_compl_iff_pi0 (j n).1 (g n)).2 (hg n)
      have hp : OrdinalSigma0 (j n).1 (f ⁻¹' (g n)ᶜ) := ih (j n).1 (j n).2 hc
      rw [preimage_compl] at hp
      exact (ordinalSigma0_compl_iff_pi0 (j n).1 (f ⁻¹' g n)).1 hp

/-- Continuous preimages preserve every ordinal multiplicative Borel class.
@isnad1 id=ordinalp.2h5v.s5.b5ecc5e2299a from=translated src=- shape=c3ef64bf vocab=a16e1a10
-/
theorem OrdinalPi0.preimage {Y : Type*} [TopologicalSpace Y] {i : Ordinal.{0}}
    {s : Set Y} (hs : OrdinalPi0 i s) {f : X → Y} (hf : Continuous f) :
    OrdinalPi0 i (f ⁻¹' s) := by
  have h := hs.compl.preimage hf
  rw [preimage_compl] at h
  exact (ordinalSigma0_compl_iff_pi0 i (f ⁻¹' s)).1 h

/-- Continuous preimages preserve every ordinal ambiguous Borel class.
@isnad1 id=ordinald.2h5v.s5.198a2f919aac from=translated src=- shape=c3ef64bf vocab=9fb9e714
-/
theorem OrdinalDelta0.preimage {Y : Type*} [TopologicalSpace Y] {i : Ordinal.{0}}
    {s : Set Y} (hs : OrdinalDelta0 i s) {f : X → Y} (hf : Continuous f) :
    OrdinalDelta0 i (f ⁻¹' s) :=
  ⟨hs.1.preimage hf, hs.2.preimage hf⟩

/-- A countable union of sets in one ordinal additive class remains in that class.
@isnad1 id=ordinals.1h3v.s5.30c0b156452d from=translated src=- shape=c5cebe2c vocab=5454517b
-/
theorem OrdinalSigma0.iUnion {i : Ordinal.{0}} {s : ℕ → Set X}
    (hs : ∀ n, OrdinalSigma0 i (s n)) : OrdinalSigma0 i (⋃ n, s n) := by
  by_cases hi0 : i = 0
  · subst i
    exact (ordinalSigma0_zero (s 0) (hs 0)).elim
  by_cases hi1 : i = 1
  · subst i
    exact ordinalSigma0_one_iff.2 (isOpen_iUnion fun n => ordinalSigma0_one_iff.1 (hs n))
  choose f j hf hsf using fun n => (ordinalSigma0_of_ne_zero_one hi0 hi1).1 (hs n)
  refine (ordinalSigma0_of_ne_zero_one hi0 hi1).2
    ⟨fun k => f k.unpair.1 k.unpair.2, fun k => j k.unpair.1 k.unpair.2,
      fun k => hf k.unpair.1 k.unpair.2, ?_⟩
  rw [Set.iUnion_unpair]
  simp_rw [hsf]

/-- A countable intersection of sets in one ordinal multiplicative class remains in that class.
@isnad1 id=ordinalp.1h3v.s5.d22aa9e159a9 from=translated src=- shape=c5cebe2c vocab=ddc690b6
-/
theorem OrdinalPi0.iInter {i : Ordinal.{0}} {s : ℕ → Set X}
    (hs : ∀ n, OrdinalPi0 i (s n)) : OrdinalPi0 i (⋂ n, s n) := by
  have h := OrdinalSigma0.iUnion fun n => (hs n).compl
  simpa using h.compl

/-- A binary union of sets in one ordinal additive class remains in that class.
@isnad1 id=ordinals.2h4v.s5.f8b6a66c7487 from=translated src=- shape=ffb9e2f3 vocab=5ceaabde
-/
theorem OrdinalSigma0.union {i : Ordinal.{0}} {s t : Set X}
    (hs : OrdinalSigma0 i s) (ht : OrdinalSigma0 i t) : OrdinalSigma0 i (s ∪ t) := by
  have h : OrdinalSigma0 i (⋃ n : ℕ, if n = 0 then s else t) :=
    OrdinalSigma0.iUnion fun n => by
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
  · rintro ⟨n, hn⟩
    by_cases h0 : n = 0
    · exact Or.inl (by simpa [h0] using hn)
    · exact Or.inr (by simpa [h0] using hn)

/-- A binary intersection of sets in one ordinal multiplicative class remains in that class.
@isnad1 id=ordinalp.2h4v.s5.10e5e0b920d5 from=translated src=- shape=ffb9e2f3 vocab=9fe54647
-/
theorem OrdinalPi0.inter {i : Ordinal.{0}} {s t : Set X}
    (hs : OrdinalPi0 i s) (ht : OrdinalPi0 i t) : OrdinalPi0 i (s ∩ t) := by
  have h : OrdinalPi0 i (⋂ n : ℕ, if n = 0 then s else t) :=
    OrdinalPi0.iInter fun n => by
      split_ifs
      · exact hs
      · exact ht
  convert h using 1
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · rintro ⟨hsx, htx⟩ n
    by_cases h0 : n = 0
    · simpa [h0]
    · simpa [h0]
  · intro hx
    exact ⟨by simpa using hx 0, by simpa using hx 1⟩

/-- Ordinal additive classes are monotone in their index in a perfectly normal space.
@isnad1 id=ordinals.2h4v.s5.20e99c895dc2 from=translated src=- shape=328d8547 vocab=4eee23b7
-/
theorem OrdinalSigma0.mono [PerfectlyNormalSpace X] {i k : Ordinal.{0}} (hik : i ≤ k)
    {s : Set X} (hs : OrdinalSigma0 i s) : OrdinalSigma0 k s := by
  by_cases hk0 : k = 0
  · have hi0 : i = 0 := bot_unique (hik.trans_eq hk0)
    subst i
    exact (ordinalSigma0_zero s hs).elim
  by_cases hk1 : k = 1
  · rcases eq_or_lt_of_le (hk1 ▸ hik) with hi1 | hi0
    · simpa [hi1, hk1] using hs
    · have : i = 0 := Order.lt_one_iff.mp hi0
      subst i
      exact (ordinalSigma0_zero s hs).elim
  by_cases hi0 : i = 0
  · subst i
    exact (ordinalSigma0_zero s hs).elim
  by_cases hi1 : i = 1
  · subst i
    have h1k : (1 : Ordinal) < k :=
      lt_of_le_of_ne (Order.one_le_iff_ne_zero.mpr hk0) (Ne.symm hk1)
    have hs2 : Sigma0 2 s :=
      (sigma0_one_of_isOpen (ordinalSigma0_one_iff.1 hs)).mono_succ
    obtain ⟨f, hf, rfl⟩ := sigma0_two_iff_eq_iUnion_isClosed.1 hs2
    refine (ordinalSigma0_of_ne_zero_one hk0 hk1).2
      ⟨f, fun _ => ⟨1, h1k⟩, ?_, rfl⟩
    intro n
    exact ordinalPi0_one_iff.2 (hf n)
  obtain ⟨f, j, hf, rfl⟩ := (ordinalSigma0_of_ne_zero_one hi0 hi1).1 hs
  refine (ordinalSigma0_of_ne_zero_one hk0 hk1).2
    ⟨f, fun n => ⟨(j n).1, (j n).2.trans_le hik⟩, hf, rfl⟩

/-- Ordinal multiplicative classes are monotone in their index in a perfectly normal space.
@isnad1 id=ordinalp.2h4v.s5.939a5892bec2 from=translated src=- shape=328d8547 vocab=9062e777
-/
theorem OrdinalPi0.mono [PerfectlyNormalSpace X] {i k : Ordinal.{0}} (hik : i ≤ k)
    {s : Set X} (hs : OrdinalPi0 i s) : OrdinalPi0 k s := by
  simpa using hs.compl.mono hik |>.compl

/-- Ordinal ambiguous classes are monotone in their index in a perfectly normal space.
@isnad1 id=ordinald.2h4v.s5.feeecdd58fb4 from=translated src=- shape=328d8547 vocab=7cc1ed5f
-/
theorem OrdinalDelta0.mono [PerfectlyNormalSpace X] {i k : Ordinal.{0}} (hik : i ≤ k)
    {s : Set X} (hs : OrdinalDelta0 i s) : OrdinalDelta0 k s :=
  ⟨hs.1.mono hik, hs.2.mono hik⟩

/-- A binary intersection of sets in one ordinal additive class remains in that class in a
perfectly normal space.
@isnad1 id=ordinals.2h4v.s5.5f170f07152b from=translated src=- shape=455c9c31 vocab=cfa0bad5
-/
theorem OrdinalSigma0.inter [PerfectlyNormalSpace X] {i : Ordinal.{0}} {s t : Set X}
    (hs : OrdinalSigma0 i s) (ht : OrdinalSigma0 i t) : OrdinalSigma0 i (s ∩ t) := by
  by_cases hi0 : i = 0
  · subst i
    exact (ordinalSigma0_zero s hs).elim
  by_cases hi1 : i = 1
  · subst i
    exact ordinalSigma0_one_iff.2 ((ordinalSigma0_one_iff.1 hs).inter
      (ordinalSigma0_one_iff.1 ht))
  obtain ⟨f, j, hf, rfl⟩ := (ordinalSigma0_of_ne_zero_one hi0 hi1).1 hs
  obtain ⟨g, k, hg, rfl⟩ := (ordinalSigma0_of_ne_zero_one hi0 hi1).1 ht
  refine (ordinalSigma0_of_ne_zero_one hi0 hi1).2
    ⟨fun n => f n.unpair.1 ∩ g n.unpair.2,
      fun n => ⟨max (j n.unpair.1).1 (k n.unpair.2).1,
        by
          change max (j n.unpair.1).1 (k n.unpair.2).1 < i
          exact max_lt (j n.unpair.1).2 (k n.unpair.2).2⟩, ?_, ?_⟩
  · intro n
    exact ((hf n.unpair.1).mono (le_max_left _ _)).inter
      ((hg n.unpair.2).mono (le_max_right _ _))
  · symm
    change (⋃ n : ℕ, f (Nat.unpair n).1 ∩ g (Nat.unpair n).2) = _
    rw [Set.iUnion_unpair (fun a b => f a ∩ g b)]
    ext x
    simp only [mem_iUnion, mem_inter_iff]
    constructor
    · rintro ⟨a, b, hfa, hgb⟩
      exact ⟨⟨a, hfa⟩, ⟨b, hgb⟩⟩
    · rintro ⟨⟨a, hfa⟩, ⟨b, hgb⟩⟩
      exact ⟨a, b, hfa, hgb⟩

/-- Ordinal ambiguous classes are closed under binary intersections in perfectly normal spaces.
@isnad1 id=ordinald.2h4v.s5.929c084495c4 from=translated src=- shape=455c9c31 vocab=1715da21
-/
theorem OrdinalDelta0.inter [PerfectlyNormalSpace X] {i : Ordinal.{0}} {s t : Set X}
    (hs : OrdinalDelta0 i s) (ht : OrdinalDelta0 i t) : OrdinalDelta0 i (s ∩ t) :=
  ⟨hs.1.inter ht.1, hs.2.inter ht.2⟩

/-- Every ordinal additive-class set has a Borel code.
@isnad1 id=ex.1h3v.s5.a36bee93edb1 from=translated src=- shape=98dc3a72 vocab=a04c439e
-/
theorem OrdinalSigma0.exists_borelCode {i : Ordinal.{0}} {s : Set X}
    (hs : OrdinalSigma0 i s) : ∃ c : BorelCode X, c.eval = s :=
  BorelCode.borelMeasurableSet_iff_exists_code.1 hs.measurableSet

end DescriptiveSetTheory
