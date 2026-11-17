import Tengoku.TutteHomotopyLean.TutteFormalization.ContractionRank

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
BG-01 interval transport of flats and hyperplanes across contraction by a flat.
These statements implement the background correspondence used in lem:separation.
-/

namespace TutteFormalization

open scoped Matroid

variable {α : Type*} {M : Matroid α} [M.Finite] {F H G : Set α}

omit [M.Finite] in
/--
@isnad1 id=isflat.2h4v.s5.7f3cbbc0276c from=translated src=- shape=87d9ad31 vocab=67639782
-/
theorem flat_sdiff_contract (hH : M.IsFlat H) (hFH : F ⊆ H) :
    (M ／ F).IsFlat (H \ F) := by
  apply (M ／ F).isFlat_iff_closure_eq.mpr
  simp only [M.contract_closure_eq, Set.sdiff_union_of_subset hFH, hH.closure]

omit [M.Finite] in
/--
@isnad1 id=isflat.2h4v.s5.0fc57cc3ff07 from=translated src=- shape=913868ed vocab=4cb959e4
-/
theorem flat_union_of_contract_flat (hF : M.IsFlat F) (hG : (M ／ F).IsFlat G) :
    M.IsFlat (G ∪ F) := by
  have hg : M.closure (G ∪ F) \ F = G := by
    simpa only [M.contract_closure_eq] using hG.closure
  have hFC : F ⊆ M.closure (G ∪ F) :=
    M.subset_closure_of_subset' Set.subset_union_right hF.subset_ground
  apply M.isFlat_iff_closure_eq.mpr
  calc
    M.closure (G ∪ F) = (M.closure (G ∪ F) \ F) ∪ F :=
      (Set.sdiff_union_of_subset hFC).symm
    _ = G ∪ F := congrArg (fun S => S ∪ F) hg

/--
@isnad1 id=ishyperp.3h4v.s5.e29b479b6e47 from=translated src=- shape=6f51ace7 vocab=e53ab435
-/
theorem hyperplane_sdiff_contract (hF : M.IsFlat F) (hH : IsHyperplane M H)
    (hFH : F ⊆ H) : IsHyperplane (M ／ F) (H \ F) := by
  apply isHyperplane_of_natRank (flat_sdiff_contract hH.1 hFH)
  have hHr := natRank_contract_add F (H \ F) hF.subset_ground
    (Set.sdiff_subset_sdiff_left hH.1.subset_ground)
  have hEr := natRank_contract_add F (M.E \ F) hF.subset_ground Set.Subset.rfl
  rw [Set.sdiff_union_of_subset hFH] at hHr
  rw [Set.sdiff_union_of_subset hF.subset_ground] at hEr
  have hr := hyperplane_natRank hH
  change natRank (M ／ F) (H \ F) + 1 = natRank (M ／ F) (M.E \ F)
  omega

/--
@isnad1 id=ishyperp.2h4v.s5.81f067fba69b from=translated src=- shape=c9bf7d7f vocab=f166ae28
-/
theorem hyperplane_union_of_contract (hF : M.IsFlat F) (hG : IsHyperplane (M ／ F) G) :
    IsHyperplane M (G ∪ F) := by
  apply isHyperplane_of_natRank (flat_union_of_contract_flat hF hG.1)
  have hGr := natRank_contract_add F G hF.subset_ground hG.1.subset_ground
  have hEr := natRank_contract_add F (M.E \ F) hF.subset_ground Set.Subset.rfl
  rw [Set.sdiff_union_of_subset hF.subset_ground] at hEr
  have hr := hyperplane_natRank hG
  change natRank (M ／ F) G + 1 = natRank (M ／ F) (M.E \ F) at hr
  omega

omit [M.Finite] in
/--
@isnad1 id=iff.2h4v.s5.423259526fb3 from=translated src=- shape=5027582a vocab=db9f4ff9
-/
theorem indecomposable_sdiff_contract_iff (hH : M.IsFlat H) (hFH : F ⊆ H) :
    Indecomposable (M ／ F) (H \ F) ↔ Indecomposable M H := by
  have heq : (M ／ F) ／ (H \ F) = M ／ H := by
    rw [Matroid.contract_contract, Set.union_sdiff_self, Set.union_eq_right.mpr hFH]
  constructor
  · intro h
    exact ⟨hH, heq ▸ h.2⟩
  · intro h
    exact ⟨flat_sdiff_contract hH hFH, heq ▸ h.2⟩

/--
@isnad1 id=indecomp.0h2v.s3.2da437ab5c15 from=translated src=- shape=54f98053 vocab=9c430c91
-/
theorem ground_indecomposable (M : Matroid α) [M.Finite] : Indecomposable M M.E := by
  refine ⟨M.ground_isFlat,
    connected_of_empty_isFlat_of_rank_le_one (contract_empty_isFlat M.ground_isFlat) ?_⟩
  change natRank (M ／ M.E) (M.E \ M.E) ≤ 1
  simp [natRank_empty]

end TutteFormalization
