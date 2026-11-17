import Tengoku.TutteHomotopyLean.TutteFormalization.PathOperations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} {Γ : Set (Set α)}

/-- S2: only the cut is normalized; the existing paths are unchanged.-/
def cutPlus (M : Matroid α) (Γ : Set (Set α)) : Set (Set α) := Γ ∪ {M.E}

theorem cutPlus_modular (hΓ : ModularCut M Γ) : ModularCut M (cutPlus M Γ) where
  isFlat F h := by
    rcases h with h | h
    · exact hΓ.isFlat F h
    · exact Set.mem_singleton_iff.mp h ▸ M.ground_isFlat
  upward F G h hG hFG := by
    rcases h with h | h
    · exact Or.inl (hΓ.upward F G h hG hFG)
    · right
      have heq : F = M.E := h
      exact Set.Subset.antisymm hG.subset_ground (heq ▸ hFG)
  inter_mem F G hF hG hm := by
    rcases hF with hF | hF <;> rcases hG with hG | hG
    · exact Or.inl (hΓ.inter_mem F G hF hG hm)
    · have heq : G = M.E := hG
      simpa only [heq, Set.inter_eq_left.mpr hm.1.subset_ground] using
        (show F ∈ cutPlus M Γ from Or.inl hF)
    · have heq : F = M.E := hF
      simpa only [heq, Set.inter_eq_right.mpr hm.2.1.subset_ground] using
        (show G ∈ cutPlus M Γ from Or.inl hG)
    · have heqF : F = M.E := hF
      have heqG : G = M.E := hG
      simp [cutPlus, heqF, heqG]

theorem hyperplane_off_cutPlus {H : Set α} (hH : IsHyperplane M H) :
    H ∉ cutPlus M Γ ↔ H ∉ Γ := by
  simp [cutPlus, hH.2.1]

theorem off_cutPlus (p : TuttePath M) : p.Off (cutPlus M Γ) ↔ p.Off Γ := by
  exact forall_congr' fun i => hyperplane_off_cutPlus (p.isHyperplane i)

theorem cutPlus_eq_of_nonempty (hΓ : ModularCut M Γ) (hne : Γ.Nonempty) :
    cutPlus M Γ = Γ := by
  obtain ⟨F, hF⟩ := hne
  have hE := hΓ.upward F M.E hF M.ground_isFlat (hΓ.isFlat F hF).subset_ground
  exact Set.union_eq_left.mpr (Set.singleton_subset_iff.mpr hE)

/-- Closedness is an equality, not an implication used as a nullity definition.-/
def Closed (p : TuttePath M) : Prop := p.origin = p.terminus

theorem constant_closed (H : Set α) (hH : IsHyperplane M H) :
    Closed (TuttePath.constant H hH) := rfl
end TutteFormalization.Homotopy
