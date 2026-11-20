/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Relational.BinaryEnergy
import Tengoku.RegularityLemmata.RegularityLemmata.Graph.Regularity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The one-step palette energy increment

Phase 9 unit 4 (design freeze in `ARCHITECTURE.md`): a partition that is not
palette-regular has a refinement gaining `ε⁵` of palette energy, with the **existing
graph part-count recurrence** `k ↦ k · 2^(2k)`.

The proof resolves **one** bad palette color: a failure yields a bad color `c`
(`exists_bad_of_not_isBinaryPaletteRegular`); the existing directed
`exists_refinement_energy_increment` applied to `HasBinaryPairPalette M c` produces a
refinement `Q ≤ P` gaining `ε⁵` for that color. Every other palette color's energy is
refinement-monotone, so none can lose energy, and the aggregate palette energy gains at
least `ε⁵`. Witnesses are **not** atomized for every color simultaneously — the
part-count bound is exactly the single-color graph bound.
-/

namespace RegularityLemmata

open FirstOrder

variable {L : FirstOrder.Language} [FiniteRelational L] {V : Type*} [DecidableEq V]
  {s : Finset V} {ε : ℝ}

/-- **The one-step palette increment.**
@isnad1 id=ex.2h6v.s7.afc9f1dc5738 from=translated src=- shape=18692f46 vocab=36bfc178
-/
theorem exists_binaryPalette_refinement_energy_increment (M : FiniteRelModel L V)
    {P : Finpartition s} (hε : 0 < ε) (hbad : ¬IsBinaryPaletteRegular M ε P) :
    ∃ Q : Finpartition s, Q ≤ P
      ∧ binaryPaletteEnergy M P + ε ^ 5 ≤ binaryPaletteEnergy M Q
      ∧ Q.parts.card ≤ P.parts.card * 2 ^ (2 * P.parts.card) := by
  obtain ⟨c, hc⟩ := exists_bad_of_not_isBinaryPaletteRegular hbad
  obtain ⟨Q, hQle, hgain, hcard⟩ :=
    exists_refinement_energy_increment (HasBinaryPairPalette M c) P hε hc
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

/-- Sanity: an already palette-regular partition cannot trigger the increment.
@isnad1 id=not.1h6v.s5.bc60013319b5 from=translated src=- shape=30c5c3d3 vocab=1ef93226
-/
theorem not_not_isBinaryPaletteRegular_of_isBinaryPaletteRegular
    {M : FiniteRelModel L V} {P : Finpartition s}
    (h : IsBinaryPaletteRegular M ε P) : ¬¬IsBinaryPaletteRegular M ε P :=
  not_not_intro h

/-! ### Tests and adversarial examples -/

section Tests

-- Statement-level instance of the increment at concrete types.

end Tests

end RegularityLemmata
