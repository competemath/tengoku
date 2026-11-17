/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Borel.Hierarchy
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Universal.BaireParameters

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Operations for ordinal-indexed universal relations

For a countable ordinal `i > 1`, enumerate the positive levels below `i`. A Baire parameter can
then select one such level and retain a Baire payload for a vertical section at that level. This
file proves that indexed section union has exactly the ordinal additive complexity prescribed by
`OrdinalSigma0`, and that it preserves universality.

The positive restriction is essential: level zero contains no sets, so no universal relation can
represent it. Components at level zero in an arbitrary hierarchy witness are impossible and are
eliminated before parameters are packed.
-/

open Cardinal Ordinal Set TopologicalSpace

universe u

namespace DescriptiveSetTheory

variable {X : Type u}

/-- The type of positive ordinal levels strictly below `i`.-/
abbrev PositiveBorelLevelBelow (i : Ordinal.{0}) := Set.Ioo (0 : Ordinal) i

/-- The positive levels below a countable Borel level form a countable type.-/
theorem countable_positiveBorelLevelBelow {i : Ordinal.{0}}
    (hi : IsCountableBorelLevel i) : Countable (PositiveBorelLevelBelow i) := by
  letI : Countable (Set.Iio i) := countable_Iio_of_isCountableBorelLevel hi
  apply Function.Injective.countable (f := fun x : PositiveBorelLevelBelow i =>
    (⟨x.1, x.2.2⟩ : Set.Iio i))
  intro a b h
  apply Subtype.ext
  exact congrArg (fun x : Set.Iio i => (x.1 : Ordinal)) h

/-- A canonical natural-number enumeration of all positive levels below a countable `i > 1`.-/
noncomputable def positiveBorelLevelSequence (i : Ordinal.{0}) (hi : (1 : Ordinal) < i)
    (hic : IsCountableBorelLevel i) : ℕ → PositiveBorelLevelBelow i := by
  letI : Countable (PositiveBorelLevelBelow i) := countable_positiveBorelLevelBelow hic
  exact Set.enumerateCountable Set.countable_univ ⟨1, zero_lt_one, hi⟩

/-- The canonical sequence reaches every positive level below `i`.-/
theorem surjective_positiveBorelLevelSequence (i : Ordinal.{0}) (hi : (1 : Ordinal) < i)
    (hic : IsCountableBorelLevel i) :
    Function.Surjective (positiveBorelLevelSequence i hi hic) := by
  letI : Countable (PositiveBorelLevelBelow i) := countable_positiveBorelLevelBelow hic
  rw [← Set.range_eq_univ]
  simpa [positiveBorelLevelSequence] using
    (Set.range_enumerateCountable_of_mem (Set.countable_univ :
      (Set.univ : Set (PositiveBorelLevelBelow i)).Countable)
      (Set.mem_univ (⟨1, zero_lt_one, hi⟩ : PositiveBorelLevelBelow i)))

/-- Vertical sections with Baire parameters commute with relation complementation.-/
@[simp] theorem verticalSection_compl_baireParameters (U : Set ((ℕ → ℕ) × X)) (p : ℕ → ℕ) :
    verticalSection Uᶜ p = (verticalSection U p)ᶜ :=
  rfl

/-- Complementing a universal ordinal additive relation gives a universal multiplicative one.-/
theorem IsUniversalFor.compl_ordinalSigma0 [TopologicalSpace X] {i : Ordinal.{0}}
    {U : Set ((ℕ → ℕ) × X)} (hU : IsUniversalFor (OrdinalSigma0 i) U) :
    IsUniversalFor (OrdinalPi0 i) Uᶜ := by
  intro s
  constructor
  · intro hs
    obtain ⟨p, hp⟩ := (hU sᶜ).1 ((ordinalSigma0_compl_iff_pi0 i s).2 hs)
    refine ⟨p, ?_⟩
    rw [verticalSection_compl_baireParameters, hp]
    simp
  · rintro ⟨p, hp⟩
    have hsection : OrdinalSigma0 i (verticalSection U p) := (hU _).2 ⟨p, rfl⟩
    have hcompl := hsection.compl
    rw [← verticalSection_compl_baireParameters U p, hp] at hcompl
    exact hcompl

/-- Indexed Baire section union builds an additive relation at level `i` from multiplicative
relations at selected positive levels below `i`.-/
theorem ordinalSigma0_baireIndexedIUnion [TopologicalSpace X]
    {i : Ordinal.{0}} (hi : (1 : Ordinal) < i)
    (j : ℕ → PositiveBorelLevelBelow i) {U : ℕ → Set ((ℕ → ℕ) × X)}
    (hU : ∀ k, OrdinalPi0 (j k).1 (U k)) : OrdinalSigma0 i (baireIndexedIUnion U) := by
  have hi0 : i ≠ 0 := ne_of_gt (zero_lt_one.trans hi)
  have hi1 : i ≠ 1 := ne_of_gt hi
  let f : ℕ → Set ((ℕ → ℕ) × X) := fun z =>
    baireSelector z.unpair.1 z.unpair.2 ∩ baireUnpackProd z.unpair.1 ⁻¹' U z.unpair.2
  let level : ℕ → Set.Iio i := fun z => ⟨(j z.unpair.2).1, (j z.unpair.2).2.2⟩
  refine (ordinalSigma0_of_ne_zero_one hi0 hi1).2 ⟨f, level, ?_, ?_⟩
  · intro z
    have hselector :
        OrdinalPi0 (j z.unpair.2).1 (baireSelector (X := X) z.unpair.1 z.unpair.2) :=
      ordinalPi0_of_isClopen (j z.unpair.2).2.1
        (isOpen_baireSelector z.unpair.1 z.unpair.2)
        (isClosed_baireSelector z.unpair.1 z.unpair.2)
    have hpayload :
        OrdinalPi0 (j z.unpair.2).1 (baireUnpackProd z.unpair.1 ⁻¹' U z.unpair.2) :=
      (hU z.unpair.2).preimage (continuous_baireUnpackProd z.unpair.1)
    exact hselector.inter hpayload
  · rw [baireIndexedIUnion_eq_iUnion]
    exact (Set.iUnion_unpair fun n k =>
      baireSelector n k ∩ baireUnpackProd n ⁻¹' U k).symm

/-- Indexed Baire section union preserves universality at any countable ordinal level above one.-/
theorem isUniversalFor_baireIndexedIUnion_ordinal [TopologicalSpace X] {i : Ordinal.{0}}
    (hi : (1 : Ordinal) < i) (j : ℕ → PositiveBorelLevelBelow i)
    (hj : Function.Surjective j) {U : ℕ → Set ((ℕ → ℕ) × X)}
    (hU : ∀ k, IsUniversalFor (OrdinalPi0 (j k).1) (U k)) :
    IsUniversalFor (OrdinalSigma0 i) (baireIndexedIUnion U) := by
  have hi0 : i ≠ 0 := ne_of_gt (zero_lt_one.trans hi)
  have hi1 : i ≠ 1 := ne_of_gt hi
  intro s
  constructor
  · intro hs
    obtain ⟨f, level, hf, rfl⟩ := (ordinalSigma0_of_ne_zero_one hi0 hi1).1 hs
    have hpositive : ∀ n, 0 < (level n).1 := by
      intro n
      by_contra hn
      have hz : (level n).1 = 0 := bot_unique (not_lt.mp hn)
      exact ordinalPi0_zero (f n) (by simpa [hz] using hf n)
    let positiveLevel : ℕ → PositiveBorelLevelBelow i := fun n =>
      ⟨(level n).1, hpositive n, (level n).2⟩
    choose k hk using fun n => hj (positiveLevel n)
    have hfk : ∀ n, OrdinalPi0 (j (k n)).1 (f n) := by
      intro n
      rw [hk n]
      exact hf n
    choose p hp using fun n => (hU (k n) (f n)).1 (hfk n)
    refine ⟨bairePack (fun n => baireCons (k n) (p n)), ?_⟩
    rw [verticalSection_baireIndexedIUnion]
    simp_rw [baireUnpack_pack, baireHead_cons, baireTail_cons, hp]
  · rintro ⟨p, rfl⟩
    refine (ordinalSigma0_of_ne_zero_one hi0 hi1).2
      ⟨fun n => verticalSection
          (U (baireHead (baireUnpack p n))) (baireTail (baireUnpack p n)),
        fun n => ⟨(j (baireHead (baireUnpack p n))).1,
          (j (baireHead (baireUnpack p n))).2.2⟩, ?_,
        verticalSection_baireIndexedIUnion U p⟩
    intro n
    exact (hU (baireHead (baireUnpack p n)) _).2
      ⟨baireTail (baireUnpack p n), rfl⟩

end DescriptiveSetTheory
