/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Graph.Uniformity
import Tengoku.RegularityLemmata.RegularityLemmata.Partition.Energy

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bad mass and weak regularity of a partition

An ordered pair of **distinct** parts is `ε`-bad when it fails `ε`-uniformity (diagonal
pairs are excluded here — they are charged or discarded only at the simple-graph
bridge, matching the energy convention of including them in `energy`).

`badMassNum` is the raw mass `Σ |C||D|` over bad ordered pairs; `badMass` its
normalization by `|s|²` under the library's zero-denominator convention. A partition is
**`ε`-regular** (`IsRegularPartition`, Szemerédi-style partition regularity — "weak
regularity" is reserved for the Frieze–Kannan cut-norm notion in
`RegularityLemmata/Graph/CutNorm.lean`) when its normalized bad mass is at most `ε`.

Ordered off-diagonal pairs follow mathlib's `Finpartition.nonUniforms`
(`Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform`). Mathlib *counts* bad pairs
because its argument runs on equipartitions, where all cell pairs carry comparable
mass; weighting by `|C||D|` is this library's generalization to arbitrary partitions
(a recorded design decision), consistent with the mass-weighted `energy`.
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α] {s : Finset α}
variable (R : α → α → Prop) [DecidableRel R] (ε : ℝ)

/-- An ordered pair of distinct parts failing `ε`-uniformity.-/
def IsBadPair (C D : Finset α) : Prop :=
  C ≠ D ∧ ¬ IsUniformPair R C D ε

open Classical in
/-- Raw bad mass: `Σ |C| · |D|` over the `ε`-bad ordered pairs of parts.-/
noncomputable def badMassNum (P : Finpartition s) : ℝ :=
  ∑ uv ∈ (P.parts ×ˢ P.parts).filter (fun uv => IsBadPair R ε uv.1 uv.2),
    (uv.1.card : ℝ) * uv.2.card

/-- Normalized bad mass, in `[0, 1]`; `0` on the empty ground set.-/
noncomputable def badMass (P : Finpartition s) : ℝ :=
  badMassNum R ε P / (s.card : ℝ) ^ 2

/-- `ε`-regularity of a partition: the normalized bad mass is at most `ε`.-/
def IsRegularPartition (P : Finpartition s) : Prop :=
  badMass R ε P ≤ ε

variable {P : Finpartition s}

/--
@isnad1 id=le.0h5v.s5.1219de66d34e from=translated src=- shape=d264cd23 vocab=2ad5a4e5
-/
theorem badMassNum_nonneg : 0 ≤ badMassNum R ε P :=
  Finset.sum_nonneg fun uv _ => by positivity

/--
@isnad1 id=le.0h5v.s5.7a3b2afca5f2 from=translated src=- shape=d264cd23 vocab=9b1ebece
-/
theorem badMass_nonneg : 0 ≤ badMass R ε P :=
  div_nonneg (badMassNum_nonneg R ε) (by positivity)

/--
@isnad1 id=le.0h5v.s6.097640d0fdd4 from=translated src=- shape=13790038 vocab=c531251d
-/
theorem badMassNum_le_sq : badMassNum R ε P ≤ (s.card : ℝ) ^ 2 := by
  classical
  calc badMassNum R ε P
      ≤ ∑ uv ∈ P.parts ×ˢ P.parts, (uv.1.card : ℝ) * uv.2.card := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun uv _ _ => by positivity
    _ = (∑ A ∈ P.parts, (A.card : ℝ)) * (∑ B ∈ P.parts, (B.card : ℝ)) := by
        rw [Finset.sum_mul_sum, Finset.sum_product]
    _ = (s.card : ℝ) ^ 2 := by rw [sum_card_parts_cast, sq]

/--
@isnad1 id=le.0h5v.s5.e0c77824e589 from=translated src=- shape=76e036eb vocab=9b1ebece
-/
theorem badMass_le_one : badMass R ε P ≤ 1 := by
  unfold badMass
  rcases eq_or_ne ((s.card : ℝ)) 0 with h | h
  · rw [h]
    norm_num
  · have hpos : (0 : ℝ) < (s.card : ℝ) :=
      lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm h)
    rw [div_le_one (by positivity)]
    exact badMassNum_le_sq R ε

/-- Bad mass is antitone in the tolerance: a pair bad at a larger `ε'` is bad at any
smaller `ε`.
@isnad1 id=le.1h6v.s5.a0aed90f143b from=translated src=- shape=0cc029e3 vocab=2ad5a4e5
-/
theorem badMassNum_anti {ε ε' : ℝ} (hεε : ε ≤ ε') :
    badMassNum R ε' P ≤ badMassNum R ε P := by
  classical
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun uv huv => ?_)
    fun uv _ _ => by positivity
  rw [Finset.mem_filter] at huv ⊢
  refine ⟨huv.1, huv.2.1, fun hunif => huv.2.2 (hunif.mono hεε)⟩

/--
@isnad1 id=le.1h6v.s5.23e599e23c0d from=translated src=- shape=0cc029e3 vocab=9b1ebece
-/
theorem badMass_anti {ε ε' : ℝ} (hεε : ε ≤ ε') : badMass R ε' P ≤ badMass R ε P :=
  div_le_div_of_nonneg_right (badMassNum_anti R hεε) (by positivity) |>.trans_eq rfl

/-- Regularity is monotone in the tolerance.
@isnad1 id=isregula.2h6v.s5.964fa3bbff3c from=translated src=- shape=a1cb1fab vocab=574f8efd
-/
theorem IsRegularPartition.mono {ε ε' : ℝ} (hεε : ε ≤ ε')
    (h : IsRegularPartition R ε P) : IsRegularPartition R ε' P :=
  le_trans (badMass_anti R hεε) (le_trans h hεε)

/-- Everything is `1`-regular.
@isnad1 id=isregula.0h4v.s5.1c9d14dbd656 from=translated src=- shape=59a30b72 vocab=0b9a54ab
-/
theorem isRegularPartition_one : IsRegularPartition R 1 P := badMass_le_one R 1

/-- **Raw regularity conversion**: a regular partition has raw bad mass at most
`ε·|s|²`.
@isnad1 id=le.1h5v.s6.868a4cb21218 from=translated src=- shape=be99551f vocab=ba581ae0
-/
theorem badMassNum_le_of_isRegularPartition (h : IsRegularPartition R ε P) :
    badMassNum R ε P ≤ ε * (s.card : ℝ) ^ 2 := by
  rcases eq_or_ne ((s.card : ℝ)) 0 with h0 | h0
  · have hle : badMassNum R ε P ≤ (s.card : ℝ) ^ 2 := badMassNum_le_sq R ε
    rw [h0] at hle ⊢
    simpa using hle
  · have hpos : (0 : ℝ) < (s.card : ℝ) ^ 2 := by
      have : (0 : ℝ) < (s.card : ℝ) := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm h0)
      positivity
    rw [IsRegularPartition, badMass, div_le_iff₀ hpos] at h
    linarith [h]

/-! ### Tests and adversarial examples -/

-- A concrete bad pair: `R a b ↔ a = 0` on `Fin 4`, cells {0,1} and {2,3}. The whole
-- block has density 1/2; the sub-block {0} × {2,3} has density 1 — deviation 1/2 > 1/4.

end RegularityLemmata
