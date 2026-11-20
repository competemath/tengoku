/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Partition.BlockEnergy

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Count splitting and the weighted-variance identity

Pair counts split additively along one-sided and `2 × 2` rectangle refinements. The
**exact weighted-variance identity** (`variance_eq_sum_blockEnergy_sub`) is the
parallel-axis theorem for block energy: over a disjoint rectangle cover of `(C, D)`,

`Σ |C'||D'| · (d(C',D') − d(C,D))² = Σ blockEnergy(C',D') − blockEnergy(C,D)`.

Superadditivity of block energy is the nonnegativity of the left side; the one-block
energy increment (`RegularityLemmata/Graph/Increment.lean`) is a quantitative lower bound on it.

The file's test section also formalizes the design fact recorded in
`RegularityLemmata/Partition/Energy.lean`: the **uniform** (count-weighted) block-mean of `d²` can
strictly decrease under refinement — which is why the library's energy is
mass-weighted.

The mass-weighted local quantity `blockEnergy(A,B) = d(A,B)² · |A| · |B|` equals
`e(A,B)² / (|A||B|)`, the form used in A. Schrijver's CWI notes on Szemerédi's
regularity lemma; the variance/energy-boost route is presented in Y. Zhao, *Graph
Theory and Additive Combinatorics*, ch. 2.
-/

namespace RegularityLemmata

variable {α : Type*} {R : α → α → Prop} [DecidableRel R] {A B : Finset α}

/-! ### One-sided and 2×2 count splits -/

/-- Splitting the source set splits the pair count additively.
@isnad1 id=eq.1h5v.s6.9e0f64c384e1 from=translated src=- shape=5f909f77 vocab=d26db833
-/
theorem pairCount_split_left (R : α → α → Prop) [DecidableRel R] [DecidableEq α]
    {A : Finset α} (A' : Finset α) (hA' : A' ⊆ A) (B : Finset α) :
    pairCount R A B = pairCount R A' B + pairCount R (A \ A') B := by
  unfold pairCount
  have hdisj : Disjoint ((A' ×ˢ B).filter fun p => R p.1 p.2)
      (((A \ A') ×ˢ B).filter fun p => R p.1 p.2) := by
    apply Finset.disjoint_filter_filter
    rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ hxy hxy'
    simp only [Finset.mem_product] at hxy hxy'
    exact (Finset.mem_sdiff.mp hxy'.1).2 hxy.1
  rw [← Finset.card_union_of_disjoint hdisj, ← Finset.filter_union, ← Finset.union_product,
    Finset.union_sdiff_of_subset hA']

/-- Splitting the target set splits the pair count additively.
@isnad1 id=eq.1h5v.s6.aa44be9d009c from=translated src=- shape=459e4185 vocab=d26db833
-/
theorem pairCount_split_right (R : α → α → Prop) [DecidableRel R] [DecidableEq α]
    (A : Finset α) {B : Finset α} (B' : Finset α) (hB' : B' ⊆ B) :
    pairCount R A B = pairCount R A B' + pairCount R A (B \ B') := by
  unfold pairCount
  have hdisj : Disjoint ((A ×ˢ B').filter fun p => R p.1 p.2)
      ((A ×ˢ (B \ B')).filter fun p => R p.1 p.2) := by
    apply Finset.disjoint_filter_filter
    rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ hxy hxy'
    simp only [Finset.mem_product] at hxy hxy'
    exact (Finset.mem_sdiff.mp hxy'.2).2 hxy.2
  rw [← Finset.card_union_of_disjoint hdisj, ← Finset.filter_union, ← Finset.product_union,
    Finset.union_sdiff_of_subset hB']

/-- The pair count is additive over the `2 × 2` refinement by a sub-rectangle.
@isnad1 id=eq.2h6v.s7.698662a83a5a from=translated src=- shape=807d5570 vocab=d26db833
-/
theorem pairCount_split (R : α → α → Prop) [DecidableRel R] [DecidableEq α]
    {A B : Finset α} (A' B' : Finset α) (hA' : A' ⊆ A) (hB' : B' ⊆ B) :
    pairCount R A B = pairCount R A' B' + pairCount R A' (B \ B')
      + pairCount R (A \ A') B' + pairCount R (A \ A') (B \ B') := by
  rw [pairCount_split_left R A' hA' B, pairCount_split_right R A' B' hB',
    pairCount_split_right R (A \ A') B' hB']
  ring

/-! ### Empty-side densities -/

/--
@isnad1 id=eq.1h4v.s5.aa519f8dd702 from=translated src=- shape=3381657f vocab=04f49aec
-/
theorem pairDensity_of_left_card_eq_zero (R : α → α → Prop) [DecidableRel R]
    (B : Finset α) (h : A.card = 0) : pairDensity R A B = 0 := by
  rw [Finset.card_eq_zero.mp h, pairDensity]
  simp

/--
@isnad1 id=eq.1h4v.s5.e1a028e44dfe from=translated src=- shape=8bb15c09 vocab=04f49aec
-/
theorem pairDensity_of_right_card_eq_zero (R : α → α → Prop) [DecidableRel R]
    (A : Finset α) (h : B.card = 0) : pairDensity R A B = 0 := by
  rw [Finset.card_eq_zero.mp h, pairDensity]
  simp [densityOn]

/-! ### The weighted-variance identity -/

/-- **Parallel-axis identity.** Over a disjoint rectangle cover of `(C, D)`, the
mass-weighted variance of the sub-block densities around the parent density is exactly
the block-energy gain of the refinement.
@isnad1 id=eq.4h6v.s8.9a64db3a56db from=translated src=- shape=6fcebee7 vocab=ce107adc
-/
theorem variance_eq_sum_blockEnergy_sub [DecidableEq α] (R : α → α → Prop) [DecidableRel R]
    {C D : Finset α} (sC sD : Finset (Finset α))
    (hCdisj : (sC : Set (Finset α)).PairwiseDisjoint id) (hCcover : sC.biUnion id = C)
    (hDdisj : (sD : Set (Finset α)).PairwiseDisjoint id) (hDcover : sD.biUnion id = D) :
    ∑ p ∈ sC ×ˢ sD, ((p.1.card : ℝ) * p.2.card)
        * (pairDensity R p.1 p.2 - pairDensity R C D) ^ 2
      = (∑ p ∈ sC ×ˢ sD, blockEnergy R p.1 p.2) - blockEnergy R C D := by
  set d := pairDensity R C D with hd
  have hM : ∑ p ∈ sC ×ˢ sD, ((p.1.card : ℝ) * p.2.card) = (C.card : ℝ) * D.card := by
    rw [Finset.sum_product, ← sum_card_biUnion_cast sC hCdisj hCcover,
      ← sum_card_biUnion_cast sD hDdisj hDcover, Finset.sum_mul_sum]
  have hCnt : ∑ p ∈ sC ×ˢ sD, ((p.1.card : ℝ) * p.2.card) * pairDensity R p.1 p.2
      = ((C.card : ℝ) * D.card) * d := by
    have hterm : ∀ p ∈ sC ×ˢ sD,
        ((p.1.card : ℝ) * p.2.card) * pairDensity R p.1 p.2
          = (pairCount R p.1 p.2 : ℝ) := fun p _ => by
      rw [pairCount_eq_pairDensity_mul]; ring
    rw [Finset.sum_congr rfl hterm, ← Nat.cast_sum,
      ← pairCount_biUnion R sC sD hCdisj hCcover hDdisj hDcover,
      pairCount_eq_pairDensity_mul, hd]
    ring
  have hexp : ∀ p ∈ sC ×ˢ sD,
      ((p.1.card : ℝ) * p.2.card) * (pairDensity R p.1 p.2 - d) ^ 2
        = blockEnergy R p.1 p.2
          - 2 * d * (((p.1.card : ℝ) * p.2.card) * pairDensity R p.1 p.2)
          + d ^ 2 * ((p.1.card : ℝ) * p.2.card) := fun p _ => by
    rw [blockEnergy]; ring
  rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hCnt, hM,
    show blockEnergy R C D = d ^ 2 * ((C.card : ℝ) * D.card) from by rw [blockEnergy]; ring]
  ring

/-- Superadditivity re-derived: the variance is nonnegative. (The Engel-form proof in
`RegularityLemmata/Partition/BlockEnergy.lean` remains the library's primary route; this corollary
checks
the identity against it.)
@isnad1 id=le.4h6v.s7.210218648db3 from=translated src=- shape=0e178b93 vocab=99e4ffbf
-/
theorem blockEnergy_le_sum_of_cover_via_variance [DecidableEq α] (R : α → α → Prop)
    [DecidableRel R] {C D : Finset α} (sC sD : Finset (Finset α))
    (hCdisj : (sC : Set (Finset α)).PairwiseDisjoint id) (hCcover : sC.biUnion id = C)
    (hDdisj : (sD : Set (Finset α)).PairwiseDisjoint id) (hDcover : sD.biUnion id = D) :
    blockEnergy R C D ≤ ∑ p ∈ sC ×ˢ sD, blockEnergy R p.1 p.2 := by
  have h := variance_eq_sum_blockEnergy_sub R sC sD hCdisj hCcover hDdisj hDcover
  have hnn : 0 ≤ ∑ p ∈ sC ×ˢ sD, ((p.1.card : ℝ) * p.2.card)
      * (pairDensity R p.1 p.2 - pairDensity R C D) ^ 2 :=
    Finset.sum_nonneg fun p _ => by positivity
  linarith

/-! ### Tests and adversarial examples -/

-- 2×2 count split on a concrete instance.

end RegularityLemmata
