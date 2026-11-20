/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Finite.PairDensity
import Tengoku.RegularityLemmata.RegularityLemmata.Finite.Inequalities
import Tengoku.RegularityLemmata.RegularityLemmata.Partition.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Block energy and superadditivity

The mass-weighted local energy of an ordered block `(A, B)` is
`pairDensity R A B ² · |A| · |B|`. Its key property is superadditivity under disjoint
covers (an Engel-form/Cauchy–Schwarz consequence), specialized to refinement fibers in
`blockEnergy_le_sum_refined` — the engine behind energy monotonicity of the partition
energy (`RegularityLemmata/Partition/Energy.lean`).
-/

namespace RegularityLemmata

variable {α : Type*} {s : Finset α}
variable {R : α → α → Prop} [DecidableRel R] {A B : Finset α}

/-- Mass-weighted local energy of the ordered block `(A, B)`.-/
noncomputable def blockEnergy (R : α → α → Prop) [DecidableRel R] (A B : Finset α) : ℝ :=
  pairDensity R A B ^ 2 * (A.card : ℝ) * (B.card : ℝ)

/--
@isnad1 id=le.0h4v.s5.a8bbeefea610 from=translated src=- shape=a8d6c262 vocab=6efb6162
-/
theorem blockEnergy_nonneg : 0 ≤ blockEnergy R A B := by
  unfold blockEnergy
  have := pairDensity_nonneg (R := R) (A := A) (B := B)
  positivity

/--
@isnad1 id=le.0h4v.s5.d6cf825244e4 from=translated src=- shape=326fcde0 vocab=4fbc7750
-/
theorem blockEnergy_le_mass : blockEnergy R A B ≤ (A.card : ℝ) * B.card := by
  unfold blockEnergy
  have h1 := pairDensity_le_one (R := R) (A := A) (B := B)
  have h0 := pairDensity_nonneg (R := R) (A := A) (B := B)
  have hA : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
  have hB : (0 : ℝ) ≤ B.card := Nat.cast_nonneg _
  have hd2 : pairDensity R A B ^ 2 ≤ 1 := by nlinarith
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd2 hA) hB
  simpa using this

/-- Empty left side kills the pair count.
@isnad1 id=eq.1h4v.s5.503a0a3e6276 from=translated src=- shape=1d236d93 vocab=ee54b545
-/
theorem pairCount_of_left_card_eq_zero (R : α → α → Prop) [DecidableRel R]
    (B : Finset α) (h : A.card = 0) : pairCount R A B = 0 := by
  rw [Finset.card_eq_zero.mp h]
  simp [pairCount]

/-- Empty right side kills the pair count.
@isnad1 id=eq.1h4v.s5.fe38473a25c8 from=translated src=- shape=632ddbad vocab=ee54b545
-/
theorem pairCount_of_right_card_eq_zero (R : α → α → Prop) [DecidableRel R]
    (A : Finset α) (h : B.card = 0) : pairCount R A B = 0 := by
  rw [Finset.card_eq_zero.mp h]
  simp [pairCount]

/-- Block energy as `(pair count)² / mass`, valid also for zero mass (both sides `0`).
@isnad1 id=eq.0h4v.s6.7f0e82fa356f from=translated src=- shape=5cc3a2fe vocab=346df16b
-/
theorem blockEnergy_eq_count_sq_div (R : α → α → Prop) [DecidableRel R] (X Y : Finset α) :
    blockEnergy R X Y = (pairCount R X Y : ℝ) ^ 2 / ((X.card : ℝ) * (Y.card : ℝ)) := by
  unfold blockEnergy
  rw [pairDensity_eq_count_div]
  rcases eq_or_ne ((X.card : ℝ) * (Y.card : ℝ)) 0 with hm | hm
  · rcases mul_eq_zero.mp hm with h | h <;> rw [h] <;> simp
  · have hX : (X.card : ℝ) ≠ 0 := fun h => hm (by rw [h]; ring)
    have hY : (Y.card : ℝ) ≠ 0 := fun h => hm (by rw [h]; ring)
    field_simp

/-- **Superadditivity.** Refining `(C, D)` into the rectangles of disjoint covers never
decreases the total block energy (Engel form over the cover rectangles).
@isnad1 id=le.4h6v.s7.a9a3c02f8d91 from=translated src=- shape=6ca9e3c3 vocab=57d37a21
-/
theorem blockEnergy_superadditive [DecidableEq α] (R : α → α → Prop) [DecidableRel R]
    {C D : Finset α} (sC sD : Finset (Finset α))
    (hCdisj : (sC : Set (Finset α)).PairwiseDisjoint id) (hCcover : sC.biUnion id = C)
    (hDdisj : (sD : Set (Finset α)).PairwiseDisjoint id) (hDcover : sD.biUnion id = D) :
    blockEnergy R C D ≤ ∑ C' ∈ sC, ∑ D' ∈ sD, blockEnergy R C' D' := by
  have hcount : ∑ p ∈ sC ×ˢ sD, (pairCount R p.1 p.2 : ℝ) = (pairCount R C D : ℝ) := by
    rw [← Nat.cast_sum, ← pairCount_biUnion R sC sD hCdisj hCcover hDdisj hDcover]
  have hmass : ∑ p ∈ sC ×ˢ sD, ((p.1.card : ℝ) * (p.2.card : ℝ))
      = (C.card : ℝ) * (D.card : ℝ) := by
    rw [Finset.sum_product, ← sum_card_biUnion_cast sC hCdisj hCcover,
      ← sum_card_biUnion_cast sD hDdisj hDcover, Finset.sum_mul_sum]
  have hgnn : ∀ p ∈ sC ×ˢ sD, 0 ≤ (p.1.card : ℝ) * (p.2.card : ℝ) := fun p _ => by
    positivity
  have hfg0 : ∀ p ∈ sC ×ˢ sD, (p.1.card : ℝ) * (p.2.card : ℝ) = 0 →
      (pairCount R p.1 p.2 : ℝ) = 0 := by
    intro p _ h
    rcases mul_eq_zero.mp h with h1 | h2
    · have hc : p.1.card = 0 := by exact_mod_cast h1
      simp [pairCount_of_left_card_eq_zero R p.2 hc]
    · have hc : p.2.card = 0 := by exact_mod_cast h2
      simp [pairCount_of_right_card_eq_zero R p.1 hc]
  have htitu := titu_finset (fun p => (pairCount R p.1 p.2 : ℝ))
    (fun p => (p.1.card : ℝ) * (p.2.card : ℝ)) (sC ×ˢ sD) hgnn hfg0
  rw [hcount, hmass, ← blockEnergy_eq_count_sq_div R C D] at htitu
  refine htitu.trans (le_of_eq ?_)
  rw [Finset.sum_product]
  exact Finset.sum_congr rfl fun C' _ =>
    Finset.sum_congr rfl fun D' _ => (blockEnergy_eq_count_sq_div R C' D').symm

/-- Superadditivity along refinement fibers: the block energy of a `P`-block is at most
the summed block energies of its refined `Q`-sub-blocks.
@isnad1 id=le.3h7v.s7.a1c43e82ac4b from=translated src=- shape=f1c645a9 vocab=e6f40783
-/
theorem blockEnergy_le_sum_refined [DecidableEq α] {P Q : Finpartition s} (hQ : Q ≤ P)
    (R : α → α → Prop) [DecidableRel R] {C D : Finset α}
    (hC : C ∈ P.parts) (hD : D ∈ P.parts) :
    blockEnergy R C D ≤ ∑ C' ∈ Q.parts.filter (· ⊆ C), ∑ D' ∈ Q.parts.filter (· ⊆ D),
      blockEnergy R C' D' := by
  refine blockEnergy_superadditive R _ _ ?_ (biUnion_filter_subset_eq hQ hC) ?_
    (biUnion_filter_subset_eq hQ hD)
  · exact Q.supIndep.pairwiseDisjoint.subset
      (by rw [Finset.coe_subset]; exact Finset.filter_subset _ _)
  · exact Q.supIndep.pairwiseDisjoint.subset
      (by rw [Finset.coe_subset]; exact Finset.filter_subset _ _)

/-! ### Tests and adversarial examples -/

-- An empty side gives zero block energy.

end RegularityLemmata
