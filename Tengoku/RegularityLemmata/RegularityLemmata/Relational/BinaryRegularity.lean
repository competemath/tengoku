/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Relational.BinaryIncrement
import Tengoku.RegularityLemmata.RegularityLemmata.Relational.BinaryProfile
import Tengoku.RegularityLemmata.RegularityLemmata.Relational.GraphAdapter

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bounded binary-palette regularity

Phase 9 unit 5 (design freeze in `ARCHITECTURE.md`): the weak summit. The palette
energy lives in `[0, 1]` and every non-regular step gains `ε⁵`, so `⌈1/ε⁵⌉` steps
suffice (`binaryPaletteRegularity_iterate`) — the **same fuel** as the graph ladder,
independent of the palette count, thanks to the energy bound of `1`.

The summit `exists_binaryPalette_regular_refinement` runs the iteration from
`refineByBinaryProfile P` (which refines both `P` and the vertex-profile partition),
so the output `Q` refines `P`, refines the profile partition, is simultaneously
regular for every palette color, and has at most `binaryRegularityBound L ε #P.parts`
cells. It asserts **nothing** about relation symbols of arity `> 2`.
-/

namespace RegularityLemmata

open FirstOrder

variable {L : FirstOrder.Language} [FiniteRelational L] {V : Type*} [DecidableEq V]
  {s : Finset V} {ε : ℝ}

/-! ### The fuel iteration -/

/-- **Fuel-parametrized palette iteration.** From palette energy within `t · ε⁵` of
the ceiling `1`, `t` weak steps reach a palette-regular refinement.
@isnad1 id=ex.2h7v.s7.e5d926284f93 from=translated src=- shape=7bccc281 vocab=7c066607
-/
theorem binaryPaletteRegularity_iterate (M : FiniteRelModel L V) (hε : 0 < ε) :
    ∀ (t : ℕ) (P : Finpartition s),
      1 - (t : ℝ) * ε ^ 5 ≤ binaryPaletteEnergy M P →
      ∃ Q : Finpartition s, Q ≤ P ∧ IsBinaryPaletteRegular M ε Q ∧
        Q.parts.card ≤ regularityBound t P.parts.card := by
  intro t
  induction t with
  | zero =>
    intro P hbudget
    refine ⟨P, le_rfl, ?_, le_regularityBound 0 _⟩
    by_contra hcon
    obtain ⟨Q, _, hinc, _⟩ :=
      exists_binaryPalette_refinement_energy_increment M hε hcon
    have h1 : binaryPaletteEnergy M Q ≤ 1 := binaryPaletteEnergy_le_one M Q
    have h2 : (1 : ℝ) ≤ binaryPaletteEnergy M P := by simpa using hbudget
    have hε5 : (0 : ℝ) < ε ^ 5 := by positivity
    linarith
  | succ t IH =>
    intro P hbudget
    by_cases hreg : IsBinaryPaletteRegular M ε P
    · exact ⟨P, le_rfl, hreg, le_regularityBound _ _⟩
    · obtain ⟨P', hP'P, hinc, hcard'⟩ :=
        exists_binaryPalette_refinement_energy_increment M hε hreg
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

/-- Palette regularity from a profile-respecting starting partition, with the graph
fuel `⌈1/ε⁵⌉`.
@isnad1 id=ex.1h6v.s7.f21eb0e4e814 from=translated src=- shape=45501502 vocab=d4bb97f8
-/
theorem exists_binaryPalette_regular_refinement_of_profiled (M : FiniteRelModel L V)
    (P : Finpartition s) (hε : 0 < ε) :
    ∃ Q : Finpartition s, Q ≤ P ∧ IsBinaryPaletteRegular M ε Q ∧
      Q.parts.card ≤ regularityBound ⌈1 / ε ^ 5⌉₊ P.parts.card := by
  refine binaryPaletteRegularity_iterate M hε _ P ?_
  have h0 : (0 : ℝ) ≤ binaryPaletteEnergy M P := binaryPaletteEnergy_nonneg M P
  have hε5 : (0 : ℝ) < ε ^ 5 := by positivity
  have ht : (1 : ℝ) ≤ (⌈1 / ε ^ 5⌉₊ : ℝ) * ε ^ 5 := by
    calc (1 : ℝ) = 1 / ε ^ 5 * ε ^ 5 := by field_simp
      _ ≤ (⌈1 / ε ^ 5⌉₊ : ℝ) * ε ^ 5 := mul_le_mul_of_nonneg_right (Nat.le_ceil _) hε5.le
  linarith

/-! ### The host-independent bound and the summit -/

/-- The vertex-profile part budget: `2^(#unary + #binary)`.-/
def binaryProfileBound (L : FirstOrder.Language) [FiniteRelational L] : ℕ :=
  2 ^ (Fintype.card (L.Relations 1) + Fintype.card (L.Relations 2))

/--
@isnad1 id=eq.0h1v.s7.c5e5365640f6 from=translated src=- shape=003df33a vocab=fc39c9e8
-/
theorem binaryProfileBound_eq_card (L : FirstOrder.Language) [FiniteRelational L] :
    binaryProfileBound L = Fintype.card (BinaryVertexProfile L) :=
  (card_binaryVertexProfile).symm

/-- The iteration fuel `⌈1/ε⁵⌉`, independent of the palette count.-/
noncomputable def binaryRegularityFuel (ε : ℝ) : ℕ := ⌈1 / ε ^ 5⌉₊

/-- The host-independent part-count bound of the summit.-/
noncomputable def binaryRegularityBound (L : FirstOrder.Language) [FiniteRelational L]
    (ε : ℝ) (k : ℕ) : ℕ :=
  regularityBound (binaryRegularityFuel ε) (k * binaryProfileBound L)

/-- **The weak binary-palette regularity summit.** Every finite binary-reduct model
admits a refinement of `P` that also refines the vertex-profile partition, is
simultaneously `ε`-regular for every two-way palette color, and has at most
`binaryRegularityBound L ε #P.parts` cells — host-independent. It asserts nothing
about relation symbols of arity greater than two.
@isnad1 id=ex.1h6v.s7.3b666f12e9fa from=translated src=- shape=85eaa7b9 vocab=cea7a366
-/
theorem exists_binaryPalette_regular_refinement (M : FiniteRelModel L V)
    (P : Finpartition s) (hε : 0 < ε) :
    ∃ Q : Finpartition s, Q ≤ P ∧ Q ≤ binaryProfilePartition M s ∧
      IsBinaryPaletteRegular M ε Q ∧
      Q.parts.card ≤ binaryRegularityBound L ε P.parts.card := by
  obtain ⟨Q, hQle, hreg, hcard⟩ :=
    exists_binaryPalette_regular_refinement_of_profiled M
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

-- No binary symbols (the empty language): the fuel bound still applies; the palette
-- has a single (empty-function) color, so regularity is trivial.

end Tests

end RegularityLemmata
