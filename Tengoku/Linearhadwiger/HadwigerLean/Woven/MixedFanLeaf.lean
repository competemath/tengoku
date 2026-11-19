import Tengoku.Linearhadwiger.HadwigerLean.Woven.MixedFanSupportGraph
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Residual starts are leaves in the path-edge-supported graph
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {Z U H : Finset V} {a : ℕ}
  {P : IndexedPairs (Fin a × Fin 2) V}

private theorem support_adj_used
    (F : DoubleFan G Z H) (L : IndexedLinkage G P)
    {u v : V} (huv : (mixedSupportGraph F L).Adj u v) :
    s(u,v) ∈ mixedUsedEdges F L := by
  have h : G.Adj u v ∧
      s(u,v) ∉ G.edgeSet \ mixedUsedEdges F L := by
    simpa [mixedSupportGraph] using huv
  by_contra hnot
  exact h.2 ⟨G.mem_edgeSet.mpr h.1, hnot⟩

/-- At every vertex of U, all supported edges have the same opposite
endpoint, provided fan paths avoid U and each connector meets U only
at its own start.-/
theorem mixedSupportGraph_unique_neighbor_at_U
    (F : DoubleFan G Z H) (L : IndexedLinkage G P)
    (hfanU : ∀ slot v, v ∈ pathVertexSet (F.path slot) → v ∉ U)
    (hlinkU : ∀ slot v, v ∈ pathVertexSet (L.path slot) →
      v ∈ U → v = P.start slot)
    {u v w : V} (hu : u ∈ U)
    (huv : (mixedSupportGraph F L).Adj u v)
    (huw : (mixedSupportGraph F L).Adj u w) : v = w := by
  have edge_from_link {y : V} (huy : (mixedSupportGraph F L).Adj u y) :
      ∃ slot : Fin a × Fin 2,
        u = P.start slot ∧
        s(u,y) ∈ (L.path slot : G.Walk (P.start slot) (P.finish slot)).edges := by
    have hused := support_adj_used F L huy
    rcases hused with ⟨slot, he⟩ | ⟨slot, he⟩
    · have huF : u ∈ pathVertexSet (F.path slot) :=
        (F.path slot : G.Walk slot.1.1 (F.finish slot)).fst_mem_support_of_mem_edges he
      exact False.elim (hfanU slot u huF hu)
    · have huL : u ∈ pathVertexSet (L.path slot) :=
        (L.path slot : G.Walk (P.start slot) (P.finish slot)).fst_mem_support_of_mem_edges he
      exact ⟨slot, hlinkU slot u huL hu, he⟩
  obtain ⟨slotV, hslotV, heV⟩ := edge_from_link huv
  obtain ⟨slotW, hslotW, heW⟩ := edge_from_link huw
  have hslots : slotV = slotW :=
    L.start_injective (hslotV.symm.trans hslotW)
  subst slotW
  have hv : v = (L.path slotV : G.Walk (P.start slotV) (P.finish slotV)).snd := by
    apply SimpleGraph.Walk.IsPath.eq_snd_of_mem_edges (L.path slotV).property
    simpa [hslotV] using heV
  have hw : w = (L.path slotV : G.Walk (P.start slotV) (P.finish slotV)).snd := by
    apply SimpleGraph.Walk.IsPath.eq_snd_of_mem_edges (L.path slotV).property
    simpa [hslotW] using heW
  exact hv.trans hw.symm

/-- A vertex whose neighbor set is a singleton cannot occur internally
on a simple path.-/
theorem path_support_U_only_endpoints
    {E : SimpleGraph V} (U : Finset V)
    (hunique : ∀ u ∈ U, ∀ v w, E.Adj u v → E.Adj u w → v = w)
    {s t u : V} (p : E.Path s t)
    (hu : u ∈ U) (hp : u ∈ pathVertexSet p) :
    u = s ∨ u = t := by
  by_cases hs : u = s
  · exact Or.inl hs
  by_cases ht : u = t
  · exact Or.inr ht
  have hsub : (E.neighborSet u).Subsingleton := by
    intro v hv w hw
    exact hunique u hu v w hv hw
  have hnot := p.property.isTrail.not_mem_support_of_subsingleton_neighborSet
    hs ht hsub
  exact False.elim (hnot hp)

end Woven
end HadwigerLean
