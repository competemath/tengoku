/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Graph.BadMass
import Tengoku.RegularityLemmata.RegularityLemmata.Graph.RegularDegree

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Phase 11 unit 3: diagonal-inclusive bad mass and regularity

The diagonal-inclusive strengthening of `RegularityLemmata/Graph/BadMass.lean`, a **parallel
additive layer** (Phase 11 design freeze in `ARCHITECTURE.md`): the frozen off-diagonal
`IsBadPair`/`IsRegularPartition` surface is unchanged, because the mathlib uniformity
bridge (`RegularityLemmata/Graph/Bridge.lean`) cannot deliver diagonal control and the Phase 10
counting charges select `IsBadPair` by frozen design.

An ordered pair of parts — **including a part paired with itself** — is `ε`-bad when it
fails `ε`-uniformity (`IsBadPairDiag`, no distinctness conjunct). `badMassDiagNum` is
the raw mass over these pairs, `badMassDiag` its normalization, `IsRegularPartitionDiag`
the resulting regularity notion. Bridges: diagonal-inclusive regularity implies the
off-diagonal notion; the diagonal-inclusive bad mass decomposes exactly into the
off-diagonal bad mass plus the bad diagonal blocks; and the layer transports along
ordered reversal (`swapRel`).

Removal-grade counting needs exactly this: copies with two or three vertices in one
cell are counted on pairs `(C, C)`, about which off-diagonal regularity says nothing
(see the tests, the dual of the frozen distinction test in
`RegularityLemmata/Relational/StrongCountingLifting.lean`).
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α] {s : Finset α}
variable (R : α → α → Prop) [DecidableRel R] (ε : ℝ)

/-- An ordered pair of parts failing `ε`-uniformity — diagonal pairs included.-/
def IsBadPairDiag (C D : Finset α) : Prop :=
  ¬ IsUniformPair R C D ε

omit [DecidableEq α] in
/-- An off-diagonal bad pair is a diagonal-inclusive bad pair.
@isnad1 id=isbadpai.1h5v.s5.ff3143da7633 from=translated src=- shape=e25a5307 vocab=f7b184d0
-/
theorem IsBadPair.isBadPairDiag {C D : Finset α} (h : IsBadPair R ε C D) :
    IsBadPairDiag R ε C D :=
  h.2

open Classical in
/-- Raw diagonal-inclusive bad mass: `Σ |C| · |D|` over all `ε`-bad ordered pairs of
parts, diagonal pairs included.-/
noncomputable def badMassDiagNum (P : Finpartition s) : ℝ :=
  ∑ uv ∈ (P.parts ×ˢ P.parts).filter (fun uv => IsBadPairDiag R ε uv.1 uv.2),
    (uv.1.card : ℝ) * uv.2.card

/-- Normalized diagonal-inclusive bad mass, in `[0, 1]`; `0` on the empty ground set.-/
noncomputable def badMassDiag (P : Finpartition s) : ℝ :=
  badMassDiagNum R ε P / (s.card : ℝ) ^ 2

/-- Diagonal-inclusive `ε`-regularity of a partition.-/
def IsRegularPartitionDiag (P : Finpartition s) : Prop :=
  badMassDiag R ε P ≤ ε

variable {P : Finpartition s}

/--
@isnad1 id=le.0h5v.s5.9326e29b12cb from=translated src=- shape=d264cd23 vocab=46bbb70a
-/
theorem badMassDiagNum_nonneg : 0 ≤ badMassDiagNum R ε P :=
  Finset.sum_nonneg fun uv _ => by positivity

/--
@isnad1 id=le.0h5v.s5.9ac9ec775466 from=translated src=- shape=d264cd23 vocab=fdcd06a4
-/
theorem badMassDiag_nonneg : 0 ≤ badMassDiag R ε P :=
  div_nonneg (badMassDiagNum_nonneg R ε) (by positivity)

/--
@isnad1 id=le.0h5v.s6.245d0e3b1ad2 from=translated src=- shape=13790038 vocab=c90f25fc
-/
theorem badMassDiagNum_le_sq : badMassDiagNum R ε P ≤ (s.card : ℝ) ^ 2 := by
  classical
  calc badMassDiagNum R ε P
      ≤ ∑ uv ∈ P.parts ×ˢ P.parts, (uv.1.card : ℝ) * uv.2.card := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun uv _ _ => by positivity
    _ = (∑ A ∈ P.parts, (A.card : ℝ)) * (∑ B ∈ P.parts, (B.card : ℝ)) := by
        rw [Finset.sum_mul_sum, Finset.sum_product]
    _ = (s.card : ℝ) ^ 2 := by rw [sum_card_parts_cast, sq]

/--
@isnad1 id=le.0h5v.s5.248a57e382bd from=translated src=- shape=76e036eb vocab=fdcd06a4
-/
theorem badMassDiag_le_one : badMassDiag R ε P ≤ 1 := by
  unfold badMassDiag
  rcases eq_or_ne ((s.card : ℝ)) 0 with h | h
  · rw [h]
    norm_num
  · have hpos : (0 : ℝ) < (s.card : ℝ) :=
      lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm h)
    rw [div_le_one (by positivity)]
    exact badMassDiagNum_le_sq R ε

/-- Diagonal-inclusive bad mass is antitone in the tolerance.
@isnad1 id=le.1h6v.s5.a1af971ac902 from=translated src=- shape=0cc029e3 vocab=46bbb70a
-/
theorem badMassDiagNum_anti {ε ε' : ℝ} (hεε : ε ≤ ε') :
    badMassDiagNum R ε' P ≤ badMassDiagNum R ε P := by
  classical
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun uv huv => ?_)
    fun uv _ _ => by positivity
  rw [Finset.mem_filter] at huv ⊢
  exact ⟨huv.1, fun hunif => huv.2 (hunif.mono hεε)⟩

/--
@isnad1 id=le.1h6v.s5.4afce9359316 from=translated src=- shape=0cc029e3 vocab=fdcd06a4
-/
theorem badMassDiag_anti {ε ε' : ℝ} (hεε : ε ≤ ε') :
    badMassDiag R ε' P ≤ badMassDiag R ε P :=
  div_le_div_of_nonneg_right (badMassDiagNum_anti R hεε) (by positivity) |>.trans_eq rfl

/-- Diagonal-inclusive regularity is monotone in the tolerance.
@isnad1 id=isregula.2h6v.s5.338aefde337a from=translated src=- shape=a1cb1fab vocab=7b24926f
-/
theorem IsRegularPartitionDiag.mono {ε ε' : ℝ} (hεε : ε ≤ ε')
    (h : IsRegularPartitionDiag R ε P) : IsRegularPartitionDiag R ε' P :=
  le_trans (badMassDiag_anti R hεε) (le_trans h hεε)

/-- Everything is diagonal-inclusively `1`-regular.
@isnad1 id=isregula.0h4v.s5.e3874cf63ef9 from=translated src=- shape=59a30b72 vocab=07781f84
-/
theorem isRegularPartitionDiag_one : IsRegularPartitionDiag R 1 P :=
  badMassDiag_le_one R 1

/-- **Raw conversion**: a diagonal-inclusively regular partition has raw
diagonal-inclusive bad mass at most `ε·|s|²`.
@isnad1 id=le.1h5v.s6.0884aeb782a9 from=translated src=- shape=be99551f vocab=3d2d71bb
-/
theorem badMassDiagNum_le_of_isRegularPartitionDiag
    (h : IsRegularPartitionDiag R ε P) :
    badMassDiagNum R ε P ≤ ε * (s.card : ℝ) ^ 2 := by
  rcases eq_or_ne ((s.card : ℝ)) 0 with h0 | h0
  · have hle : badMassDiagNum R ε P ≤ (s.card : ℝ) ^ 2 := badMassDiagNum_le_sq R ε
    rw [h0] at hle ⊢
    simpa using hle
  · have hpos : (0 : ℝ) < (s.card : ℝ) ^ 2 := by
      have : (0 : ℝ) < (s.card : ℝ) := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm h0)
      positivity
    rw [IsRegularPartitionDiag, badMassDiag, div_le_iff₀ hpos] at h
    linarith [h]

/-! ### Bridges to the off-diagonal layer -/

/-- The off-diagonal bad mass is dominated by the diagonal-inclusive one.
@isnad1 id=le.0h5v.s5.99e25d9240be from=translated src=- shape=33b5ab78 vocab=7b2de365
-/
theorem badMassNum_le_badMassDiagNum : badMassNum R ε P ≤ badMassDiagNum R ε P := by
  classical
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun uv huv => ?_)
    fun uv _ _ => by positivity
  rw [Finset.mem_filter] at huv ⊢
  exact ⟨huv.1, huv.2.isBadPairDiag⟩

/--
@isnad1 id=le.0h5v.s5.8e6247a30891 from=translated src=- shape=33b5ab78 vocab=03802296
-/
theorem badMass_le_badMassDiag : badMass R ε P ≤ badMassDiag R ε P :=
  div_le_div_of_nonneg_right (badMassNum_le_badMassDiagNum R ε) (by positivity)
    |>.trans_eq rfl

/-- **Diagonal-inclusive regularity implies the frozen off-diagonal notion** — every
Phase 9/10 consumer applies unchanged through this bridge.
@isnad1 id=isregula.1h5v.s5.ca65f077a0d1 from=translated src=- shape=5b43de74 vocab=549cc6e2
-/
theorem IsRegularPartitionDiag.isRegularPartition
    (h : IsRegularPartitionDiag R ε P) : IsRegularPartition R ε P :=
  le_trans (badMass_le_badMassDiag R ε) h

open Classical in
/-- **Exact decomposition**: the diagonal-inclusive bad mass is the off-diagonal bad
mass plus the mass `|C|²` of the parts whose diagonal pair fails uniformity.
@isnad1 id=eq.0h5v.s7.813ff690c3d8 from=translated src=- shape=a45860ab vocab=3812065d
-/
theorem badMassDiagNum_eq_badMassNum_add :
    badMassDiagNum R ε P = badMassNum R ε P
      + ∑ C ∈ P.parts.filter (fun C => ¬ IsUniformPair R C C ε), (C.card : ℝ) ^ 2 := by
  rw [badMassDiagNum,
    ← Finset.sum_filter_add_sum_filter_not
      ((P.parts ×ˢ P.parts).filter fun uv => IsBadPairDiag R ε uv.1 uv.2)
      (fun uv => uv.1 ≠ uv.2)]
  congr 1
  · rw [badMassNum, Finset.filter_filter]
    refine Finset.sum_congr (Finset.filter_congr fun uv _ => ?_) fun _ _ => rfl
    show IsBadPairDiag R ε uv.1 uv.2 ∧ uv.1 ≠ uv.2 ↔ IsBadPair R ε uv.1 uv.2
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  · rw [Finset.filter_filter]
    refine Finset.sum_nbij' (fun uv => uv.1) (fun C => (C, C)) ?_ ?_ ?_ ?_ ?_
    · intro uv huv
      rw [Finset.mem_filter, Finset.mem_product] at huv
      rw [Finset.mem_filter]
      have heq : uv.1 = uv.2 := not_ne_iff.mp huv.2.2
      exact ⟨huv.1.1, heq ▸ huv.2.1⟩
    · intro C hC
      rw [Finset.mem_filter] at hC
      rw [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hC.1, hC.1⟩, hC.2, not_ne_iff.mpr rfl⟩
    · intro uv huv
      rw [Finset.mem_filter] at huv
      exact Prod.ext rfl (not_ne_iff.mp huv.2.2)
    · intro C _
      rfl
    · intro uv huv
      rw [Finset.mem_filter] at huv
      have heq : uv.1 = uv.2 := not_ne_iff.mp huv.2.2
      rw [← heq, sq]

/-! ### Ordered-reversal transport -/

omit [DecidableEq α] in
/-- Diagonal-inclusive badness transports along ordered reversal.
@isnad1 id=iff.0h5v.s5.7ca629d1edf5 from=translated src=- shape=1111c889 vocab=6a20611d
-/
theorem isBadPairDiag_swapRel_iff {C D : Finset α} :
    IsBadPairDiag (swapRel R) ε C D ↔ IsBadPairDiag R ε D C :=
  not_congr (isUniformPair_swapRel_iff R)

open Classical in
/-- Diagonal-inclusive bad mass is reversal-invariant.
@isnad1 id=eq.0h5v.s5.063c4c821a2d from=translated src=- shape=330df99f vocab=5ddbcd5b
-/
theorem badMassDiagNum_swapRel : badMassDiagNum (swapRel R) ε P = badMassDiagNum R ε P := by
  rw [badMassDiagNum, badMassDiagNum]
  refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
  · intro uv huv
    rw [Finset.mem_filter, Finset.mem_product] at huv ⊢
    exact ⟨⟨huv.1.2, huv.1.1⟩, (isBadPairDiag_swapRel_iff R ε).mp huv.2⟩
  · intro uv huv
    rw [Finset.mem_filter, Finset.mem_product] at huv ⊢
    exact ⟨⟨huv.1.2, huv.1.1⟩, (isBadPairDiag_swapRel_iff R ε).mpr huv.2⟩
  · intro uv _
    rfl
  · intro uv _
    rfl
  · intro uv _
    rw [mul_comm]
    rfl

/--
@isnad1 id=eq.0h5v.s5.a95d062f856f from=translated src=- shape=330df99f vocab=95461aeb
-/
theorem badMassDiag_swapRel : badMassDiag (swapRel R) ε P = badMassDiag R ε P := by
  rw [badMassDiag, badMassDiag, badMassDiagNum_swapRel]

/--
@isnad1 id=iff.0h5v.s5.12b9b373d8bc from=translated src=- shape=9182e674 vocab=a3d30a0f
-/
theorem isRegularPartitionDiag_swapRel_iff :
    IsRegularPartitionDiag (swapRel R) ε P ↔ IsRegularPartitionDiag R ε P := by
  rw [IsRegularPartitionDiag, IsRegularPartitionDiag, badMassDiag_swapRel]

/-! ### Tests and adversarial examples -/

-- The single-cell (indiscrete) partition of the two-point ground set, and the equality
-- relation supported inside that one cell.
private abbrev onePart : Finpartition (Finset.univ : Finset (Fin 2)) :=
  Finpartition.indiscrete (by decide)

-- The full diagonal pair fails `1/4`-uniformity: the sub-blocks `{0}` and `{1}` deviate
-- from the block density `1/2` by `1/2`.

end RegularityLemmata
