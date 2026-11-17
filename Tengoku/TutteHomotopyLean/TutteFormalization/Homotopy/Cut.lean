import Tengoku.TutteHomotopyLean.TutteFormalization.PathOperations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace TutteFormalization.Homotopy
variable {α : Type*} {M : Matroid α} {Γ : Set (Set α)}

/-- S2: only the cut is normalized; the existing paths are unchanged.-/
def cutPlus (M : Matroid α) (Γ : Set (Set α)) : Set (Set α) := Γ ∪ {M.E}

/--
@isnad1 id=modularc.1h3v.s4.0122680e2cf9 from=translated src=- shape=298fb510 vocab=3bda014d
-/
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

/--
@isnad1 id=iff.1h4v.s5.71b9c8798f2a from=translated src=- shape=ef8a1598 vocab=26e91b01
-/
theorem hyperplane_off_cutPlus {H : Set α} (hH : IsHyperplane M H) :
    H ∉ cutPlus M Γ ↔ H ∉ Γ := by
  simp [cutPlus, hH.2.1]

/--
@isnad1 id=iff.0h4v.s4.d2c2367b43ba from=translated src=- shape=6243481c vocab=a8e42912
-/
theorem off_cutPlus (p : TuttePath M) : p.Off (cutPlus M Γ) ↔ p.Off Γ := by
  exact forall_congr' fun i => hyperplane_off_cutPlus (p.isHyperplane i)

/--
@isnad1 id=eq.2h3v.s4.1a44437a6641 from=translated src=- shape=eafaf096 vocab=34818f8a
-/
theorem cutPlus_eq_of_nonempty (hΓ : ModularCut M Γ) (hne : Γ.Nonempty) :
    cutPlus M Γ = Γ := by
  obtain ⟨F, hF⟩ := hne
  have hE := hΓ.upward F M.E hF M.ground_isFlat (hΓ.isFlat F hF).subset_ground
  exact Set.union_eq_left.mpr (Set.singleton_subset_iff.mpr hE)

/-- Closedness is an equality, not an implication used as a nullity definition.-/
def Closed (p : TuttePath M) : Prop := p.origin = p.terminus

/--
@isnad1 id=closed.1h3v.s4.4d07ed6339aa from=translated src=- shape=5ac50161 vocab=6f55b246
-/
theorem constant_closed (H : Set α) (hH : IsHyperplane M H) :
    Closed (TuttePath.constant H hH) := rfl
end TutteFormalization.Homotopy
