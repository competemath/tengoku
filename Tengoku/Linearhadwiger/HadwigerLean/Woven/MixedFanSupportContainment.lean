import Tengoku.Linearhadwiger.HadwigerLean.Woven.MixedFanTrim
import Tengoku.Linearhadwiger.HadwigerLean.Woven.DoubleFanCost
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Vertex support of a mixed-fan linkage

The mixed Menger argument runs in the graph made of the supplied fan and
connector edges. A path beginning on one of those paths cannot introduce
any other vertex. This records the containment needed when routing around
the old model and the child pieces.
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {Z H : Finset V} {a : ℕ}
  {P : IndexedPairs (Fin a × Fin 2) V}

/--
@isnad1 id=le.1h11v.s7.fe0777d152d3 from=translated src=- shape=37bdd282 vocab=cbc57fc7
-/
theorem mixedSupportGraph_path_subset_used
    (F : DoubleFan G Z H) (L : IndexedLinkage G P)
    {s t : V} (p : (mixedSupportGraph F L).Path s t)
    (hs : s ∈ (F.vertexFinset : Set V) ∪ L.vertices) :
    pathVertexSet p ⊆ (F.vertexFinset : Set V) ∪ L.vertices := by
  classical
  let E := mixedSupportGraph F L
  have hedge (e : Sym2 V)
      (he : e ∈ (p : E.Walk s t).edges)
      (v : V) (hve : v ∈ e) :
      v ∈ (F.vertexFinset : Set V) ∪ L.vertices := by
    have heE : e ∈ E.edgeSet := (p : E.Walk s t).edges_subset_edgeSet he
    have heUsed : e ∈ mixedUsedEdges F L := by
      have h : e ∈ G.edgeSet ∧ e ∈ mixedUsedEdges F L := by
        simpa [E, mixedSupportGraph] using heE
      exact h.2
    rcases heUsed with ⟨slot,heslot⟩ | ⟨slot,heslot⟩
    · apply Or.inl
      change v ∈ F.vertexFinset
      apply Finset.mem_biUnion.mpr
      refine ⟨slot,Finset.mem_univ _,?_⟩
      apply List.mem_toFinset.mpr
      exact (SimpleGraph.Walk.mem_support_iff_exists_mem_edges).mpr
        (Or.inr ⟨e,heslot,hve⟩)
    · apply Or.inr
      exact L.path_subset_vertices slot
        ((SimpleGraph.Walk.mem_support_iff_exists_mem_edges).mpr
          (Or.inr ⟨e,heslot,hve⟩))
  intro v hv
  by_cases hnil : (p : E.Walk s t).Nil
  · have hst : s = t := hnil.eq
    have hsingle : pathVertexSet p = {s} :=
      pathVertexSet.eq_singleton_of_eq p hst
    rw [hsingle] at hv
    simpa using hv ▸ hs
  · obtain ⟨e,he,hve⟩ :=
      (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hnil).mp hv
    exact hedge e he v hve

end Woven
end HadwigerLean
