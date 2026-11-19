import Tengoku.Linearhadwiger.HadwigerLean.Graph.Linkedness.CoreTransfer
import Tengoku.Linearhadwiger.HadwigerLean.Graph.Linkedness.CoreFanFinal
import Tengoku.Linearhadwiger.HadwigerLean.Graph.RootedCliqueMinor
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace HadwigerLean
namespace Linkedness

noncomputable def IndexedPairs.reverse {ι V : Type*} (P : IndexedPairs ι V) : IndexedPairs ι V :=
  ⟨P.finish, P.start⟩

private theorem pathVertexSet_reverse {V : Type*} {G : SimpleGraph V}
    {s t : V} (p : G.Path s t) :
    pathVertexSet p.reverse = pathVertexSet p := by
  ext x
  simp [pathVertexSet, SimpleGraph.Path.reverse, SimpleGraph.Walk.support_reverse]

noncomputable def IndexedLinkage.reverse {ι V : Type*} {G : SimpleGraph V}
    {P : IndexedPairs ι V} (L : IndexedLinkage G P) :
    IndexedLinkage G (IndexedPairs.reverse P) where
  path := fun i => (L.path i).reverse
  disjoint := by
    intro i j hij
    change Disjoint (pathVertexSet (L.path i).reverse) (pathVertexSet (L.path j).reverse)
    rw [pathVertexSet_reverse (L.path i), pathVertexSet_reverse (L.path j)]
    exact L.disjoint hij

/-- Trim a path at its first vertex in a set, given any hit.-/
theorem FirstHit.exists_of_hit
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {s t : V}
    (p : G.Path s t) (J : Finset V)
    (hhit : ∃ x ∈ J, x ∈ pathVertexSet p) :
    Nonempty (FirstHit p J) := by
  classical
  let w : G.Walk s t := p
  have hnon : {x ∈ J | x ∈ w.support}.Nonempty := by
    obtain ⟨x, hxJ, hxP⟩ := hhit
    exact ⟨x, Finset.mem_filter.mpr ⟨hxJ, hxP⟩⟩
  obtain ⟨u, huJ, huW, hfirst⟩ :=
    w.exists_mem_support_forall_mem_support_imp_eq J hnon
  let q : G.Path s u := ⟨w.takeUntil u huW, p.property.takeUntil huW⟩
  exact ⟨{
    finish := u
    finish_mem := huJ
    path := q
    path_subset := by
      intro x hx
      exact w.support_takeUntil_subset_support huW hx
    unique_hit := by
      intro x hx hxJ
      exact hfirst x hxJ hx
  }⟩

/-- Trim a disjoint family at first hits, allowing the old finishes to lie outside the hit set.-/
theorem IndexedLinkage.trim_to_first_hit_of_hit
    {ι V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {P : IndexedPairs ι V}
    (L : IndexedLinkage G P) (J : Finset V)
    (hhit : ∀ i, ∃ x ∈ J, x ∈ pathVertexSet (L.path i)) :
    ∃ (P' : IndexedPairs ι V) (L' : IndexedLinkage G P'),
      (∀ i, P'.start i = P.start i) ∧
      (∀ i, P'.finish i ∈ J) ∧
      (∀ i x, x ∈ pathVertexSet (L'.path i) → x ∈ J → x = P'.finish i) ∧
      (∀ i, pathVertexSet (L'.path i) ⊆ pathVertexSet (L.path i)) := by
  classical
  let F (i : ι) : FirstHit (L.path i) J :=
    Classical.choice (FirstHit.exists_of_hit (L.path i) J (hhit i))
  let P' : IndexedPairs ι V := ⟨P.start, fun i => (F i).finish⟩
  let L' : IndexedLinkage G P' := {
    path := fun i => (F i).path
    disjoint := by
      intro i j hij
      exact Set.disjoint_of_subset (F i).path_subset (F j).path_subset (L.disjoint hij)
  }
  exact ⟨P', L', (fun _ => rfl), (fun i => (F i).finish_mem),
    (fun i x hx hxJ => (F i).unique_hit x hx hxJ),
    (fun i => (F i).path_subset)⟩

end Linkedness
end HadwigerLean
