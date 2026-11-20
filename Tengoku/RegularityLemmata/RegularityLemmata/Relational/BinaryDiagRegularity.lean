/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Relational.BinaryRegularity
import Tengoku.RegularityLemmata.RegularityLemmata.Graph.RegularityDiag

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Phase 11 unit 5a: diagonal-inclusive binary-palette regularity

The diagonal-inclusive twin of `RegularityLemmata/Relational/BinaryRegularity.lean` (Phase 11 design
freeze in `ARCHITECTURE.md`): simultaneous `ε`-regularity of every palette color over
**all** ordered cell pairs, diagonal pairs included, as a parallel additive layer over
the frozen off-diagonal surface.

The one-bad-color architecture is predicate-agnostic: a failure yields one bad palette
color at diagonal-inclusive bad mass exceeding `ε`, the diagonal-inclusive graph step
(`exists_refinement_energy_increment_diag`) gains `ε⁵` of that color's energy, and
every other color is refinement-monotone. The fuel `⌈1/ε⁵⌉` is unchanged (the palette
energy ceiling `1` is independent of the palette count), and the summit
`exists_binaryPaletteDiagRegular_refinement` carries the **identical host-independent
bound `binaryRegularityBound`** as the frozen Phase 9 summit — reused, not redefined.
-/

namespace RegularityLemmata

open FirstOrder

variable {L : FirstOrder.Language} [FiniteRelational L] {V : Type*} [DecidableEq V]
  {s : Finset V} {ε : ℝ}

/-- Simultaneous diagonal-inclusive `ε`-regularity of every palette color.-/
def IsBinaryPaletteDiagRegular (M : FiniteRelModel L V) (ε : ℝ) (P : Finpartition s) :
    Prop :=
  ∀ c : BinaryPairPalette L, IsRegularPartitionDiag (HasBinaryPairPalette M c) ε P

/-- **Diagonal-inclusive palette regularity implies the frozen off-diagonal notion** —
every Phase 9/10 consumer applies unchanged through this bridge.
@isnad1 id=isbinary.1h6v.s5.125b4ec54815 from=translated src=- shape=44a6d216 vocab=32c0c027
-/
theorem IsBinaryPaletteDiagRegular.isBinaryPaletteRegular {M : FiniteRelModel L V}
    {P : Finpartition s} (h : IsBinaryPaletteDiagRegular M ε P) :
    IsBinaryPaletteRegular M ε P :=
  fun c => (h c).isRegularPartition

/-- Monotone in the tolerance.
@isnad1 id=isbinary.2h7v.s5.bd4d4f6ba1cc from=translated src=- shape=0dcef97f vocab=eb4f50bf
-/
theorem IsBinaryPaletteDiagRegular.mono {M : FiniteRelModel L V} {P : Finpartition s}
    {ε ε' : ℝ} (hεε : ε ≤ ε') (h : IsBinaryPaletteDiagRegular M ε P) :
    IsBinaryPaletteDiagRegular M ε' P :=
  fun c => IsRegularPartitionDiag.mono (R := HasBinaryPairPalette M c) hεε (h c)

/-- Every partition is diagonal-inclusively palette-regular at tolerance `1`.
@isnad1 id=isbinary.0h5v.s5.37f0d35b391b from=translated src=- shape=e388e86d vocab=c2bc06bc
-/
theorem isBinaryPaletteDiagRegular_one (M : FiniteRelModel L V) (P : Finpartition s) :
    IsBinaryPaletteDiagRegular M 1 P :=
  fun _ => isRegularPartitionDiag_one _

/-- **Failure yields a bad palette color** at diagonal-inclusive bad mass.
@isnad1 id=ex.1h6v.s6.d20b76570247 from=translated src=- shape=faa9195a vocab=29630e7e
-/
theorem exists_bad_of_not_isBinaryPaletteDiagRegular {M : FiniteRelModel L V}
    {P : Finpartition s} (h : ¬IsBinaryPaletteDiagRegular M ε P) :
    ∃ c : BinaryPairPalette L, ε < badMassDiag (HasBinaryPairPalette M c) ε P := by
  rw [IsBinaryPaletteDiagRegular] at h
  push Not at h
  obtain ⟨c, hc⟩ := h
  rw [IsRegularPartitionDiag, not_le] at hc
  exact ⟨c, hc⟩

/-! ### The one-step increment -/

/-- **The one-step diagonal-inclusive palette increment**: resolve ONE bad color via
the diagonal-inclusive graph step; every other color is refinement-monotone. Growth
`k · 2^(2k)`, unchanged.
@isnad1 id=ex.2h6v.s7.d699a53f0eab from=translated src=- shape=18692f46 vocab=0ef76090
-/
theorem exists_binaryPaletteDiag_refinement_energy_increment (M : FiniteRelModel L V)
    {P : Finpartition s} (hε : 0 < ε) (hbad : ¬IsBinaryPaletteDiagRegular M ε P) :
    ∃ Q : Finpartition s, Q ≤ P
      ∧ binaryPaletteEnergy M P + ε ^ 5 ≤ binaryPaletteEnergy M Q
      ∧ Q.parts.card ≤ P.parts.card * 2 ^ (2 * P.parts.card) := by
  obtain ⟨c, hc⟩ := exists_bad_of_not_isBinaryPaletteDiagRegular hbad
  obtain ⟨Q, hQle, hgain, hcard⟩ :=
    exists_refinement_energy_increment_diag (HasBinaryPairPalette M c) P hε hc
  refine ⟨Q, hQle, ?_, hcard⟩
  have hnn : ∀ c' ∈ (Finset.univ : Finset (BinaryPairPalette L)),
      0 ≤ energy (HasBinaryPairPalette M c') Q - energy (HasBinaryPairPalette M c') P :=
    fun c' _ => sub_nonneg.mpr (energy_mono _ hQle)
  have hsingle : energy (HasBinaryPairPalette M c) Q
        - energy (HasBinaryPairPalette M c) P
      ≤ ∑ c' : BinaryPairPalette L,
          (energy (HasBinaryPairPalette M c') Q
            - energy (HasBinaryPairPalette M c') P) :=
    Finset.single_le_sum hnn (Finset.mem_univ c)
  have hsum : binaryPaletteEnergy M Q - binaryPaletteEnergy M P
      = ∑ c' : BinaryPairPalette L,
          (energy (HasBinaryPairPalette M c') Q
            - energy (HasBinaryPairPalette M c') P) := by
    rw [binaryPaletteEnergy, binaryPaletteEnergy, ← Finset.sum_sub_distrib]
  linarith

/-! ### The fuel iteration and the summit -/

/-- Fuel-parametrized diagonal-inclusive palette iteration — same fuel as the frozen
ladder.
@isnad1 id=ex.2h7v.s7.d62a71bb78c3 from=translated src=- shape=7bccc281 vocab=c4dc271c
-/
theorem binaryPaletteDiagRegularity_iterate (M : FiniteRelModel L V) (hε : 0 < ε) :
    ∀ (t : ℕ) (P : Finpartition s),
      1 - (t : ℝ) * ε ^ 5 ≤ binaryPaletteEnergy M P →
      ∃ Q : Finpartition s, Q ≤ P ∧ IsBinaryPaletteDiagRegular M ε Q ∧
        Q.parts.card ≤ regularityBound t P.parts.card := by
  intro t
  induction t with
  | zero =>
    intro P hbudget
    refine ⟨P, le_rfl, ?_, le_regularityBound 0 _⟩
    by_contra hcon
    obtain ⟨Q, _, hinc, _⟩ :=
      exists_binaryPaletteDiag_refinement_energy_increment M hε hcon
    have h1 : binaryPaletteEnergy M Q ≤ 1 := binaryPaletteEnergy_le_one M Q
    have h2 : (1 : ℝ) ≤ binaryPaletteEnergy M P := by simpa using hbudget
    have hε5 : (0 : ℝ) < ε ^ 5 := by positivity
    linarith
  | succ t IH =>
    intro P hbudget
    by_cases hreg : IsBinaryPaletteDiagRegular M ε P
    · exact ⟨P, le_rfl, hreg, le_regularityBound _ _⟩
    · obtain ⟨P', hP'P, hinc, hcard'⟩ :=
        exists_binaryPaletteDiag_refinement_energy_increment M hε hreg
      have hbudget' : 1 - (t : ℝ) * ε ^ 5 ≤ binaryPaletteEnergy M P' := by
        have hexp : ((t : ℝ) + 1) * ε ^ 5 = (t : ℝ) * ε ^ 5 + ε ^ 5 := by ring
        push_cast at hbudget
        rw [hexp] at hbudget
        linarith
      obtain ⟨Q, hQP', hQreg, hQcard⟩ := IH P' hbudget'
      refine ⟨Q, hQP'.trans hP'P, hQreg, ?_⟩
      calc Q.parts.card ≤ regularityBound t P'.parts.card := hQcard
        _ ≤ regularityBound t (P.parts.card * 2 ^ (2 * P.parts.card)) :=
            regularityBound_mono t hcard'
        _ = regularityBound (t + 1) P.parts.card := by simp only [regularityBound]

/-- Diagonal-inclusive palette regularity from any starting partition, with the graph
fuel `⌈1/ε⁵⌉`.
@isnad1 id=ex.1h6v.s7.f57b69752427 from=translated src=- shape=45501502 vocab=3695f23e
-/
theorem exists_binaryPaletteDiagRegular_refinement_of_profiled (M : FiniteRelModel L V)
    (P : Finpartition s) (hε : 0 < ε) :
    ∃ Q : Finpartition s, Q ≤ P ∧ IsBinaryPaletteDiagRegular M ε Q ∧
      Q.parts.card ≤ regularityBound ⌈1 / ε ^ 5⌉₊ P.parts.card := by
  refine binaryPaletteDiagRegularity_iterate M hε _ P ?_
  have h0 : (0 : ℝ) ≤ binaryPaletteEnergy M P := binaryPaletteEnergy_nonneg M P
  have hε5 : (0 : ℝ) < ε ^ 5 := by positivity
  have ht : (1 : ℝ) ≤ (⌈1 / ε ^ 5⌉₊ : ℝ) * ε ^ 5 := by
    calc (1 : ℝ) = 1 / ε ^ 5 * ε ^ 5 := by field_simp
      _ ≤ (⌈1 / ε ^ 5⌉₊ : ℝ) * ε ^ 5 := mul_le_mul_of_nonneg_right (Nat.le_ceil _) hε5.le
  linarith

/-- **The diagonal-inclusive palette summit**, with the **identical** host-independent
bound `binaryRegularityBound` as the frozen Phase 9 summit (reused, not redefined). It
asserts nothing about relation symbols of arity greater than two.
@isnad1 id=ex.1h6v.s7.8ceb9523dc66 from=translated src=- shape=85eaa7b9 vocab=c667f2e9
-/
theorem exists_binaryPaletteDiagRegular_refinement (M : FiniteRelModel L V)
    (P : Finpartition s) (hε : 0 < ε) :
    ∃ Q : Finpartition s, Q ≤ P ∧ Q ≤ binaryProfilePartition M s ∧
      IsBinaryPaletteDiagRegular M ε Q ∧
      Q.parts.card ≤ binaryRegularityBound L ε P.parts.card := by
  obtain ⟨Q, hQle, hreg, hcard⟩ :=
    exists_binaryPaletteDiagRegular_refinement_of_profiled M
      (refineByBinaryProfile M P) hε
  refine ⟨Q, hQle.trans (refineByBinaryProfile_le M P),
    hQle.trans (refineByBinaryProfile_le_profile M P), hreg, ?_⟩
  calc Q.parts.card
      ≤ regularityBound (binaryRegularityFuel ε) (refineByBinaryProfile M P).parts.card :=
        hcard
    _ ≤ regularityBound (binaryRegularityFuel ε) (P.parts.card * binaryProfileBound L) := by
        refine regularityBound_mono _ ?_
        rw [binaryProfileBound_eq_card]
        exact card_parts_refineByBinaryProfile_le M P
    _ = binaryRegularityBound L ε P.parts.card := rfl

/-! ### Tests and adversarial examples -/

section Tests

open FiniteRelModel

-- The diagonal-inclusive summit strengthens the frozen Phase 9 one, statement-level.

end Tests

end RegularityLemmata
