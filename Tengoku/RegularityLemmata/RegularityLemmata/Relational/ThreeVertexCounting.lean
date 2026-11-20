/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Relational.BinaryPattern
import Tengoku.RegularityLemmata.RegularityLemmata.Graph.PathCounting
import Tengoku.RegularityLemmata.RegularityLemmata.Graph.TriangleCounting
import Tengoku.RegularityLemmata.RegularityLemmata.Graph.RepeatedCellCounting

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Induced three-vertex relational counting

Phase 10 unit 6 (design freeze in `ARCHITECTURE.md`): lifting the directed graph path and
triangle counts (Units 4–5) to induced relational patterns via the palette machinery.

The palette wrappers (`abs_binaryPalettePathDensity_sub_le`,
`abs_binaryPaletteTriangleCount_sub_le`) make the colored path/triangle deliverable visible
in the relational namespace — palette-color relations `HasBinaryPairPalette M c` are just
`DecidableRel` relations, so these are direct wrappers, not new proofs.

The logical core is `preservesAndReflects_three_iff`: under nullary compatibility and
vertex-profile matching, an induced embedding of a three-vertex pattern `P` is exactly a
directed triangle in the three **forward** palette-color relations
`binaryPairPalette P {01, 02, 12}` (each palette already carries both orientations, so
`binaryPairPalette_swap` handles the reverse pairs; injectivity is not needed). The exact
box-count bridge `inducedEmbeddingCountOn_three` is then a filter congruence — both sides
count functions in the same `piFinset` — and `abs_inducedEmbeddingCountOn_three_sub_le`
combines it with the `7·ε` triangle bound.
-/

namespace RegularityLemmata

open FirstOrder FiniteRelModel

variable {L : FirstOrder.Language} [FiniteRelational L] {V : Type*} [DecidableEq V]

/-! ### Palette path and triangle wrappers -/

/-- The colored directed-path deliverable: two palette colors feed the `6·ε` path bound.
@isnad1 id=le.4h9v.s7.4527506237c2 from=translated src=- shape=c04f7b8f vocab=5f9b62f0
-/
theorem abs_binaryPalettePathDensity_sub_le (M : FiniteRelModel L V)
    (c₀₁ c₁₂ : BinaryPairPalette L) {A B C : Finset V} {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (h01 : IsUniformPair (HasBinaryPairPalette M c₀₁) A B ε)
    (h12 : IsUniformPair (HasBinaryPairPalette M c₁₂) B C ε) :
    |directedPathDensity (HasBinaryPairPalette M c₀₁) (HasBinaryPairPalette M c₁₂) A B C
        - pairDensity (HasBinaryPairPalette M c₀₁) A B
            * pairDensity (HasBinaryPairPalette M c₁₂) B C| ≤ 6 * ε :=
  abs_directedPathDensity_sub_le _ _ hε0 hε1 h01 h12

/-- The colored directed-triangle deliverable: three palette colors feed the `7·ε` bound.
@isnad1 id=le.5h10v.s8.d98df288d89a from=translated src=- shape=d2f7a6ac vocab=13390e82
-/
theorem abs_binaryPaletteTriangleCount_sub_le (M : FiniteRelModel L V)
    (c₀₁ c₀₂ c₁₂ : BinaryPairPalette L) {A B C : Finset V} {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (h01 : IsUniformPair (HasBinaryPairPalette M c₀₁) A B ε)
    (h02 : IsUniformPair (HasBinaryPairPalette M c₀₂) A C ε)
    (h12 : IsUniformPair (HasBinaryPairPalette M c₁₂) B C ε) :
    |(directedTriangleCount (HasBinaryPairPalette M c₀₁) (HasBinaryPairPalette M c₀₂)
          (HasBinaryPairPalette M c₁₂) A B C : ℝ)
        - pairDensity (HasBinaryPairPalette M c₀₁) A B
            * pairDensity (HasBinaryPairPalette M c₀₂) A C
            * pairDensity (HasBinaryPairPalette M c₁₂) B C
            * A.card * B.card * C.card|
      ≤ 7 * ε * A.card * B.card * C.card :=
  abs_directedTriangleCount_sub_le _ _ _ hε0 hε1 h01 h02 h12

/-! ### The three-vertex logical reduction -/

omit [DecidableEq V] in
/-- **The three-vertex reduction.** Under profile matching, an induced embedding of a
three-vertex pattern is exactly a directed triangle in the three forward palette colors.
Injectivity is not needed.
@isnad1 id=iff.4h5v.s8.604d22138c8a from=translated src=- shape=475e84e9 vocab=eed97397
-/
theorem preservesAndReflects_three_iff [AtMostBinary L]
    {P : FiniteRelModel L (Fin 3)} {M : FiniteRelModel L V}
    (hnull : NullaryCompatible P M) {f : Fin 3 → V}
    (h0 : binaryVertexProfile M (f 0) = binaryVertexProfile P 0)
    (h1 : binaryVertexProfile M (f 1) = binaryVertexProfile P 1)
    (h2 : binaryVertexProfile M (f 2) = binaryVertexProfile P 2) :
    PreservesAndReflects P M f ↔
      directedTriangleObs
        (HasBinaryPairPalette M (binaryPairPalette P 0 1))
        (HasBinaryPairPalette M (binaryPairPalette P 0 2))
        (HasBinaryPairPalette M (binaryPairPalette P 1 2)) f := by
  rw [preservesAndReflects_iff_profiles_palettes, directedTriangleObs]
  constructor
  · rintro ⟨_, _, hpal⟩
    exact ⟨(hpal 0 1 (by decide)).symm, (hpal 0 2 (by decide)).symm, (hpal 1 2 (by decide)).symm⟩
  · rintro ⟨hp01, hp02, hp12⟩
    refine ⟨hnull, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact h0.symm
      · exact h1.symm
      · exact h2.symm
    · intro i j hij
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hp01.symm
      · exact hp02.symm
      · show binaryPairPalette P 1 0 = binaryPairPalette M (f 1) (f 0)
        rw [binaryPairPalette_swap P 0 1, binaryPairPalette_swap M (f 0) (f 1), hp01]
      · exact absurd rfl hij
      · exact hp12.symm
      · show binaryPairPalette P 2 0 = binaryPairPalette M (f 2) (f 0)
        rw [binaryPairPalette_swap P 0 2, binaryPairPalette_swap M (f 0) (f 2), hp02]
      · show binaryPairPalette P 2 1 = binaryPairPalette M (f 2) (f 1)
        rw [binaryPairPalette_swap P 1 2, binaryPairPalette_swap M (f 1) (f 2), hp12]
      · exact absurd rfl hij

/-! ### The exact box-count bridge -/

/-- **Exact three-vertex count.** On disjoint profile-matching cells, the induced count
equals the directed triangle count of the three required palette colors.
@isnad1 id=eq.7h7v.s9.d0e634583670 from=translated src=- shape=28d82663 vocab=053c108c
-/
theorem inducedEmbeddingCountOn_three [AtMostBinary L]
    {P : FiniteRelModel L (Fin 3)} {M : FiniteRelModel L V} {A B C : Finset V}
    (hnull : NullaryCompatible P M)
    (hA : ∀ v ∈ A, binaryVertexProfile M v = binaryVertexProfile P 0)
    (hB : ∀ v ∈ B, binaryVertexProfile M v = binaryVertexProfile P 1)
    (hC : ∀ v ∈ C, binaryVertexProfile M v = binaryVertexProfile P 2)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    inducedEmbeddingCountOn P M ![A, B, C]
      = directedTriangleCount
          (HasBinaryPairPalette M (binaryPairPalette P 0 1))
          (HasBinaryPairPalette M (binaryPairPalette P 0 2))
          (HasBinaryPairPalette M (binaryPairPalette P 1 2)) A B C := by
  rw [inducedEmbeddingCountOn_of_disjoint P M (by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | (show Disjoint A B; exact hAB)
      | (show Disjoint A C; exact hAC)
      | (show Disjoint B A; exact hAB.symm)
      | (show Disjoint B C; exact hBC)
      | (show Disjoint C A; exact hAC.symm)
      | (show Disjoint C B; exact hBC.symm)),
    directedTriangleCount, tupleCount]
  refine congrArg Finset.card (Finset.filter_congr fun f hf => ?_)
  rw [Fintype.mem_piFinset] at hf
  exact preservesAndReflects_three_iff hnull (hA _ (hf 0)) (hB _ (hf 1)) (hC _ (hf 2))

/-- **Exact three-vertex count WITHOUT disjointness.** On profile-matching boxes that
may overlap or coincide, the induced count is the INJECTIVE triangle count of the
three required palette colors — the explicit injectivity condition is retained in the
count rather than derived from disjointness. This is the bridge the Phase 11
placement-strata certificate consumes on role-indexed representative boxes (whose
coarse parents may coincide while the fine boxes differ, and vice versa).
@isnad1 id=eq.4h7v.s9.8b5090cc579b from=translated src=- shape=25640d02 vocab=e684482d
-/
theorem inducedEmbeddingCountOn_three_eq_injectiveTriangleCount [AtMostBinary L]
    {P : FiniteRelModel L (Fin 3)} {M : FiniteRelModel L V} {A B C : Finset V}
    (hnull : NullaryCompatible P M)
    (hA : ∀ v ∈ A, binaryVertexProfile M v = binaryVertexProfile P 0)
    (hB : ∀ v ∈ B, binaryVertexProfile M v = binaryVertexProfile P 1)
    (hC : ∀ v ∈ C, binaryVertexProfile M v = binaryVertexProfile P 2) :
    inducedEmbeddingCountOn P M ![A, B, C]
      = injectiveTriangleCount
          (HasBinaryPairPalette M (binaryPairPalette P 0 1))
          (HasBinaryPairPalette M (binaryPairPalette P 0 2))
          (HasBinaryPairPalette M (binaryPairPalette P 1 2)) A B C := by
  rw [inducedEmbeddingCountOn, injectiveTriangleCount]
  refine congrArg Finset.card (Finset.filter_congr fun f hf => ?_)
  rw [Fintype.mem_piFinset] at hf
  have hiff := preservesAndReflects_three_iff hnull (hA _ (hf 0)) (hB _ (hf 1)) (hC _ (hf 2))
  exact ⟨fun h => ⟨hiff.mp h.2, h.1⟩, fun h => ⟨h.2, hiff.mpr h.1⟩⟩

/-! ### The induced three-vertex counting theorem -/

/-- **Induced three-vertex approximation.** On disjoint profile-matching cells with all
three required palette colors `ε`-uniform, the induced count is within `7·ε·|A||B||C|` of
the product of the three palette densities times the box volume.
@isnad1 id=le.12h8v.s10.e321707a9405 from=translated src=- shape=937fcd92 vocab=b3ea0a54
-/
theorem abs_inducedEmbeddingCountOn_three_sub_le [AtMostBinary L]
    {P : FiniteRelModel L (Fin 3)} {M : FiniteRelModel L V} {A B C : Finset V} {ε : ℝ}
    (hnull : NullaryCompatible P M)
    (hA : ∀ v ∈ A, binaryVertexProfile M v = binaryVertexProfile P 0)
    (hB : ∀ v ∈ B, binaryVertexProfile M v = binaryVertexProfile P 1)
    (hC : ∀ v ∈ C, binaryVertexProfile M v = binaryVertexProfile P 2)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (h01 : IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 0 1)) A B ε)
    (h02 : IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 0 2)) A C ε)
    (h12 : IsUniformPair (HasBinaryPairPalette M (binaryPairPalette P 1 2)) B C ε) :
    |(inducedEmbeddingCountOn P M ![A, B, C] : ℝ)
        - pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 1)) A B
            * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 0 2)) A C
            * pairDensity (HasBinaryPairPalette M (binaryPairPalette P 1 2)) B C
            * A.card * B.card * C.card|
      ≤ 7 * ε * A.card * B.card * C.card := by
  rw [inducedEmbeddingCountOn_three hnull hA hB hC hAB hAC hBC]
  exact abs_binaryPaletteTriangleCount_sub_le M _ _ _ hε0 hε1 h01 h02 h12

/-! ### Tests and adversarial examples -/

section Tests

/-- The unique model of the empty language (no relations to interpret).-/
private def emptyModel (V : Type*) : FiniteRelModel FirstOrder.Language.empty V :=
  ⟨fun {_} R _ => R.elim⟩

/-- A directed one-binary-symbol test model on `Fin 3`.-/
private def dModel (p : Fin 3 → Fin 3 → Bool) : FiniteRelModel (singleRelLang 2) (Fin 3) :=
  ⟨fun {n} _ x => if h : n = 2 then p (x (Fin.cast h.symm 0)) (x (Fin.cast h.symm 1)) else false⟩

-- **The no-disjointness bridge on COINCIDING boxes** (statement level): overlapping or
-- equal boxes are allowed; injectivity is carried by the count, not by disjointness.

end Tests

end RegularityLemmata
