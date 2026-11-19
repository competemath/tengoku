import Tengoku.Linearhadwiger.HadwigerLean.Woven.ThreeChildAssembly

import Tengoku.Linearhadwiger.HadwigerLean.Graph.RootedCliqueMinor.InducedLinkage

import Tengoku.Linearhadwiger.HadwigerLean.Graph.Linkedness.Massed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Prescribed three-child connectors inside the graph without parent roots
-/

namespace HadwigerLean
namespace Woven

variable {V ι : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V}

/-- Injective starts, injective finishes, and disjoint start/finish ranges
give disjoint indexed terminals.
@isnad1 id=disjoint.3h3v.s6.8765db3a89c9 from=translated src=- shape=bc580640 vocab=58a5ae98
-/
theorem disjointTerminals_of_injective_ends
    (P : IndexedPairs ι V)
    (hs : Function.Injective P.start)
    (ht : Function.Injective P.finish)
    (hst : Disjoint (Set.range P.start) (Set.range P.finish)) :
    P.DisjointTerminals := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases hxi with hxi | hxi <;> rcases hxj with hxj | hxj
  · exact hij (hs (hxi.symm.trans hxj))
  · exact (Set.disjoint_left.mp hst)
      ⟨i,hxi.symm⟩ ⟨j,hxj.symm⟩
  · exact (Set.disjoint_left.mp hst)
      ⟨j,hxj.symm⟩ ⟨i,hxi.symm⟩
  · exact hij (ht (hxi.symm.trans hxj))

/-- Every vertex of a linkage mapped out of an induced graph still lies
inside the inducing set.
@isnad1 id=le.0h6v.s6.7e6861f68940 from=translated src=- shape=a8542652 vocab=55aebadc
-/
theorem IndexedLinkage.mapInduce_vertices_subset
    {S : Set V} {P : IndexedPairs ι S}
    (L : IndexedLinkage (G.induce S) P) :
    (L.mapInduce).vertices ⊆ S := by
  intro v hv
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hv
  change v ∈ ((L.path i : (G.induce S).Walk
    (P.start i) (P.finish i)).map
      (SimpleGraph.Embedding.induce S).toHom).support at hi
  rw [SimpleGraph.Walk.support_map] at hi
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp hi
  exact u.property

end Woven
end HadwigerLean
