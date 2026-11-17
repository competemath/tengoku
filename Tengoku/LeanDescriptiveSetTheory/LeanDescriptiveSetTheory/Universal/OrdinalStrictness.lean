/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Universal.OrdinalHierarchy

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Strictness at countable ordinal Borel levels

The ordinal universal relations use Baire parameters. Taking Baire space itself as the object space
therefore permits the same diagonal argument as at finite Cantor levels. At every positive
countable ordinal `i`, the complement of the additive universal relation along the diagonal is in
`OrdinalPi0 i` but not `OrdinalSigma0 i`. Its complement gives the dual witness.
-/

open Cardinal Ordinal Set TopologicalSpace

namespace DescriptiveSetTheory

/-- The diagonal map from Baire space to its square.-/
def baireDiagonal (p : ℕ → ℕ) : (ℕ → ℕ) × (ℕ → ℕ) :=
  (p, p)

/-- The Baire-space diagonal map is continuous.-/
theorem continuous_baireDiagonal : Continuous baireDiagonal :=
  continuous_id.prodMk continuous_id

/-- The complement of a Baire relation pulled back along the diagonal.-/
def baireDiagonalComplement (U : Set ((ℕ → ℕ) × (ℕ → ℕ))) : Set (ℕ → ℕ) :=
  baireDiagonal ⁻¹' Uᶜ

/-- Membership in the Baire diagonal complement is failure of self-membership.-/
@[simp] theorem mem_baireDiagonalComplement {U : Set ((ℕ → ℕ) × (ℕ → ℕ))}
    {p : ℕ → ℕ} : p ∈ baireDiagonalComplement U ↔ (p, p) ∉ U :=
  Iff.rfl

/-- The diagonal complement of an ordinal additive relation is multiplicative at the same level.-/
theorem OrdinalSigma0.baireDiagonalComplement {i : Ordinal.{0}}
    {U : Set ((ℕ → ℕ) × (ℕ → ℕ))} (hU : OrdinalSigma0 i U) :
    OrdinalPi0 i (baireDiagonalComplement U) :=
  hU.compl.preimage continuous_baireDiagonal

/-- A universal ordinal additive relation cannot code its own diagonal complement.-/
theorem IsUniversalFor.not_ordinalSigma0_baireDiagonalComplement {i : Ordinal.{0}}
    {U : Set ((ℕ → ℕ) × (ℕ → ℕ))} (hU : IsUniversalFor (OrdinalSigma0 i) U) :
    ¬ OrdinalSigma0 i (baireDiagonalComplement U) := by
  intro hdiagonal
  obtain ⟨p, hp⟩ := (hU (baireDiagonalComplement U)).1 hdiagonal
  have hself := Set.ext_iff.mp hp p
  simp only [verticalSection, mem_baireDiagonalComplement, mem_ofPred_eq] at hself
  tauto

/-- A canonical multiplicative-not-additive Baire set at the positive countable level `i`.-/
noncomputable def baireOrdinalPiNotSigma (i : Ordinal.{0})
    (hic : IsCountableBorelLevel i) : Set (ℕ → ℕ) :=
  baireDiagonalComplement (baireOrdinalUniversalSigma i hic)

/-- The canonical ordinal multiplicative witness belongs to level `i`.-/
theorem ordinalPi0_baireOrdinalPiNotSigma {i : Ordinal.{0}}
    (hic : IsCountableBorelLevel i) (hi0 : 0 < i) :
    OrdinalPi0 i (baireOrdinalPiNotSigma i hic) :=
  (ordinalSigma0_baireOrdinalUniversalSigma hic hi0).baireDiagonalComplement

/-- The canonical ordinal multiplicative witness is not additive at level `i`.-/
theorem not_ordinalSigma0_baireOrdinalPiNotSigma {i : Ordinal.{0}}
    (hic : IsCountableBorelLevel i) (hi0 : 0 < i) :
    ¬ OrdinalSigma0 i (baireOrdinalPiNotSigma i hic) :=
  IsUniversalFor.not_ordinalSigma0_baireDiagonalComplement
    (isUniversalFor_baireOrdinalUniversalSigma hic hi0)

/-- A canonical additive-not-multiplicative Baire set at the positive countable level `i`.-/
noncomputable def baireOrdinalSigmaNotPi (i : Ordinal.{0})
    (hic : IsCountableBorelLevel i) : Set (ℕ → ℕ) :=
  (baireOrdinalPiNotSigma i hic)ᶜ

/-- The canonical ordinal additive witness belongs to level `i`.-/
theorem ordinalSigma0_baireOrdinalSigmaNotPi {i : Ordinal.{0}}
    (hic : IsCountableBorelLevel i) (hi0 : 0 < i) :
    OrdinalSigma0 i (baireOrdinalSigmaNotPi i hic) :=
  (ordinalPi0_baireOrdinalPiNotSigma hic hi0).compl

/-- The canonical ordinal additive witness is not multiplicative at level `i`.-/
theorem not_ordinalPi0_baireOrdinalSigmaNotPi {i : Ordinal.{0}}
    (hic : IsCountableBorelLevel i) (hi0 : 0 < i) :
    ¬ OrdinalPi0 i (baireOrdinalSigmaNotPi i hic) := by
  intro hpi
  apply not_ordinalSigma0_baireOrdinalPiNotSigma hic hi0
  simpa [baireOrdinalSigmaNotPi] using hpi.compl

/-- At every positive countable ordinal level, some Baire multiplicative set is not additive.-/
theorem exists_ordinalPi0_not_ordinalSigma0_baire {i : Ordinal.{0}}
    (hic : IsCountableBorelLevel i) (hi0 : 0 < i) :
    ∃ s : Set (ℕ → ℕ), OrdinalPi0 i s ∧ ¬ OrdinalSigma0 i s :=
  ⟨baireOrdinalPiNotSigma i hic, ordinalPi0_baireOrdinalPiNotSigma hic hi0,
    not_ordinalSigma0_baireOrdinalPiNotSigma hic hi0⟩

/-- At every positive countable ordinal level, some Baire additive set is not multiplicative.-/
theorem exists_ordinalSigma0_not_ordinalPi0_baire {i : Ordinal.{0}}
    (hic : IsCountableBorelLevel i) (hi0 : 0 < i) :
    ∃ s : Set (ℕ → ℕ), OrdinalSigma0 i s ∧ ¬ OrdinalPi0 i s :=
  ⟨baireOrdinalSigmaNotPi i hic, ordinalSigma0_baireOrdinalSigmaNotPi hic hi0,
    not_ordinalPi0_baireOrdinalSigmaNotPi hic hi0⟩

end DescriptiveSetTheory
