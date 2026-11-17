import Tengoku.TutteHomotopyLean.TutteFormalization.ContractionRank

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
BG-01 hyperplane separation follows the source's basis construction.
ST-02's modular-cut rule is then proved using the exact rank equality.
-/

namespace TutteFormalization

variable {α : Type*} {M : Matroid α} [M.Finite] {F X Y : Set α}

/-- BG-01: extend a basis of F with e, then remove e from a containing base.
@isnad1 id=ex.3h4v.s6.12030bb0a00e from=translated src=- shape=4ae65183 vocab=c6ba38ad
-/
theorem exists_hyperplane_superset_notMem (hF : M.IsFlat F) {e : α}
    (heE : e ∈ M.E) (heF : e ∉ F) :
    ∃ H : Set α, IsHyperplane M H ∧ F ⊆ H ∧ e ∉ H := by
  obtain ⟨I, hI⟩ := M.exists_isBasis F hF.subset_ground
  have heCI : e ∉ M.closure I := by
    simpa only [hI.closure_eq_closure, hF.closure] using heF
  have heI : e ∉ I := fun h => heCI (M.subset_closure I hI.indep.subset_ground h)
  have hIe : M.Indep (insert e I) := hI.indep.insert_indep_iff.mpr (Or.inl ⟨heE, heCI⟩)
  obtain ⟨B, hB, hIeB⟩ := hIe.exists_isBase_superset
  have heB : e ∈ B := hIeB (Set.mem_insert e I)
  let J := B \ {e}
  have heJ : e ∉ M.closure J := hB.indep.notMem_closure_sdiff_of_mem heB
  have hIJ : I ⊆ J := by
    intro a ha
    exact ⟨hIeB (Set.mem_insert_of_mem e ha), by simpa only [Set.mem_singleton_iff] using
      (show a ≠ e from fun h => heI (h ▸ ha))⟩
  have hFJ : F ⊆ M.closure J := by
    rw [← hF.closure, ← hI.closure_eq_closure]
    exact M.closure_mono hIJ
  have hJB : insert e J = B := by
    ext x
    simp only [J, Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff]
    by_cases hxe : x = e
    · simp [hxe, heB]
    · simp [hxe]
  have hr : M.eRk B = M.eRk J + 1 := by
    simpa only [hJB] using M.eRk_insert_eq_add_one ⟨heE, heJ⟩
  rw [hB.eRk_eq_eRank, M.eRank_def, ← cast_natRank M M.E, ← cast_natRank M J] at hr
  have hnr : natRank M (M.closure J) + 1 = natRank M M.E := by
    rw [natRank_closure]
    exact_mod_cast hr.symm
  exact ⟨M.closure J, isHyperplane_of_natRank (M.isFlat_closure _) hnr, hFJ, heJ⟩

/-- BG-01: the containing hyperplanes detect containment in a flat.
@isnad1 id=le.3h4v.s5.d2110ca9dc7c from=translated src=- shape=a4d6d2d3 vocab=edfaca18
-/
theorem subset_flat_of_forall_hyperplane (hF : M.IsFlat F) {A : Set α} (hAE : A ⊆ M.E)
    (h : ∀ H : Set α, IsHyperplane M H → F ⊆ H → A ⊆ H) : A ⊆ F := by
  intro e heA
  by_contra heF
  obtain ⟨H, hH, hFH, heH⟩ := exists_hyperplane_superset_notMem hF (hAE heA) heF
  exact heH (h H hH hFH heA)

omit [M.Finite] in
/--
@isnad1 id=eq.3h4v.s5.268e9dd452dd from=translated src=- shape=b179a160 vocab=f43c2b4d
-/
theorem hyperplane_join_eq_ground (hX : IsHyperplane M X) (hY : IsHyperplane M Y)
    (hne : X ≠ Y) : M.closure (X ∪ Y) = M.E := by
  have hXE : X ∪ Y ⊆ M.E := Set.union_subset hX.1.subset_ground hY.1.subset_ground
  have hXC : X ⊆ M.closure (X ∪ Y) := Set.subset_union_left.trans (M.subset_closure _ hXE)
  have hYC : Y ⊆ M.closure (X ∪ Y) := Set.subset_union_right.trans (M.subset_closure _ hXE)
  rcases hX.2.2 _ (M.isFlat_closure _) hXC with heq | heq
  · have hYX : Y ⊆ X := hYC.trans_eq heq
    rcases hY.2.2 X hX.1 hYX with h | h
    · exact False.elim (hne h)
    · exact False.elim (hX.2.1 h)
  · exact heq

/-- ST-02: the precise modular equality, not just distinctness of hyperplanes.
@isnad1 id=modularp.4h4v.s5.05b6dd808029 from=translated src=- shape=ee5a9d25 vocab=d65c58f7
-/
theorem hyperplanes_modularPair_of_corankTwo (hX : IsHyperplane M X)
    (hY : IsHyperplane M Y) (hne : X ≠ Y) (hc : CorankTwo M (X ∩ Y)) : ModularPair M X Y := by
  refine ⟨hX.1, hY.1, ?_⟩
  have hxr := hyperplane_natRank hX
  have hyr := hyperplane_natRank hY
  have hir : natRank M (X ∩ Y) + 2 = natRank M M.E := by
    have h := hc.2
    rw [← cast_natRank M (X ∩ Y), ← cast_natRank M M.E] at h
    exact_mod_cast h
  rw [hyperplane_join_eq_ground hX hY hne, ← cast_natRank M X, ← cast_natRank M Y,
    ← cast_natRank M (X ∩ Y), ← cast_natRank M M.E]
  exact_mod_cast (show natRank M X + natRank M Y = natRank M (X ∩ Y) + natRank M M.E by omega)

/-- ST-02 / PT-07: two cut hyperplanes with corank-two intersection put it in the cut.
@isnad1 id=mem.7h5v.s6.be94db8aa41c from=translated src=- shape=5a5b8f55 vocab=a9f21915
-/
theorem ModularCut.hyperplane_inter_mem {Γ : Set (Set α)} (hΓ : ModularCut M Γ)
    (hX : IsHyperplane M X) (hY : IsHyperplane M Y) (hne : X ≠ Y)
    (hc : CorankTwo M (X ∩ Y)) (hXΓ : X ∈ Γ) (hYΓ : Y ∈ Γ) : X ∩ Y ∈ Γ :=
  hΓ.inter_mem X Y hXΓ hYΓ (hyperplanes_modularPair_of_corankTwo hX hY hne hc)

end TutteFormalization
