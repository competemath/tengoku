import Tengoku.Linearhadwiger.HadwigerLean.Graph.Linkedness.TorsoLinkageGlue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The minimal rigid-separation reduction for the near-side torso. -/

namespace HadwigerLean
namespace Linkedness

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Roots viewed as vertices of the near-side torso.-/
noncomputable def torsoRootFinset {G : SimpleGraph V}
    (S : VertexSeparation G) (X : Finset V) : Finset S.left := by
  classical
  exact Finset.univ.filter (fun u : S.left => (u : V) ∈ X)

/--
@isnad1 id=iff.0h5v.s6.10d8c5aad7b0 from=translated src=- shape=b57c3c6f vocab=cd2f98c5
-/
@[simp] theorem mem_torsoRootFinset {G : SimpleGraph V}
    (S : VertexSeparation G) (X : Finset V) (u : S.left) :
    u ∈ torsoRootFinset S X ↔ (u : V) ∈ X := by
  simp [torsoRootFinset]

/--
@isnad1 id=eq.1h4v.s5.8076ee62a246 from=translated src=- shape=628633b9 vocab=f20c656c
-/
theorem torsoRootFinset_card {G : SimpleGraph V}
    (S : VertexSeparation G) (X : Finset V)
    (hX : (X : Set V) ⊆ S.left) :
    (torsoRootFinset S X).card = X.card := by
  classical
  have hs : ((torsoRootFinset S X : Finset S.left) : Set S.left) =
      {u : S.left | (u : V) ∈ X} := by
    ext u
    simp
  have hc := lifted_roots_card (X : Set V) S hX
  have hc' : Nat.card ((torsoRootFinset S X : Finset S.left) : Set S.left) =
      Nat.card (X : Set V) := by
    rw [hs]
    exact hc
  simpa only [Nat.card_coe_set_eq, Set.ncard_coe_finset] using hc'

/-- A proper far shore makes the near side smaller than the whole graph.
@isnad1 id=lt.1h3v.s5.39b3b665ea90 from=translated src=- shape=af43750e vocab=1f6f722c
-/
theorem left_card_lt_of_strictRight_nonempty
    {G : SimpleGraph V} (S : VertexSeparation G)
    (hfar : S.strictRight.Nonempty) :
    Nat.card S.left < Fintype.card V := by
  classical
  obtain ⟨x,hxR,hxNotL⟩ := hfar
  have hss : S.left ⊂ (Set.univ : Set V) := by
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨Set.subset_univ _, ?_⟩
    intro heq
    exact hxNotL (heq.symm ▸ Set.mem_univ x)
  have hc := Set.ncard_lt_ncard hss
  change S.left.ncard < Fintype.card V
  simpa only [Set.ncard_univ, Nat.card_eq_fintype_card] using hc
end Linkedness
end HadwigerLean
