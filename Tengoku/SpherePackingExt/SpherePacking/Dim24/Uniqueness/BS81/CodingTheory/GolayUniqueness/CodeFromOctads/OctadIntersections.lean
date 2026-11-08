module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.SteinerDefs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Pairwise intersection bound in `S(5,8,24)`

This file records the basic fact that two distinct blocks in a Steiner system `S(5,8,24)` meet in
at most four points. It is a purely Steiner-system consequence (no coding theory yet).
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniquenessSteps.CodeFromOctads

noncomputable section

open SteinerSystem

private lemma inter_card_eq_eight_iff_eq
    (S : SteinerSystem 24 8 5)
    {B B' : Finset (Fin 24)}
    (hB : B ∈ S.blocks) (hB' : B' ∈ S.blocks) :
    (B ∩ B').card = 8 ↔ B = B' := by
  constructor
  · intro hcard
    have hBcard : B.card = 8 := S.block_card B hB
    have hB'card : B'.card = 8 := S.block_card B' hB'
    have hBB' : B ∩ B' = B := by
      refine Finset.eq_of_subset_of_card_le (Finset.inter_subset_left) ?_
      simpa [hBcard] using le_of_eq hcard.symm
    have hB'B : B ∩ B' = B' := by
      have hcard' : (B' ∩ B).card = 8 := by simpa [Finset.inter_comm] using hcard
      have hB'B' : B' ∩ B = B' := by
        refine Finset.eq_of_subset_of_card_le (Finset.inter_subset_left) ?_
        simpa [hB'card] using le_of_eq hcard'.symm
      simpa [Finset.inter_comm] using hB'B'
    exact hBB'.symm.trans hB'B
  · intro hEq
    subst hEq
    have hBcard : B.card = 8 := S.block_card B hB
    simp [hBcard]

end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniquenessSteps.CodeFromOctads
