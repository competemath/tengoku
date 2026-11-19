import Tengoku.Linearhadwiger.HadwigerLean.Woven.MixedFanFinal
import Tengoku.Linearhadwiger.HadwigerLean.Woven.Basic
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The graph supported only by the two supplied fan families
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {Z H : Finset V} {a : ℕ}
  {P : IndexedPairs (Fin a × Fin 2) V}

/-- Precisely the old edges used by either the proxy double fan or the
residual-to-hub linkage.-/
def mixedUsedEdges (F : DoubleFan G Z H) (L : IndexedLinkage G P) :
    Set (Sym2 V) :=
  {e | ∃ slot, e ∈ (F.path slot : G.Walk slot.1.1 (F.finish slot)).edges} ∪
    {e | ∃ slot, e ∈ (L.path slot : G.Walk (P.start slot) (P.finish slot)).edges}

/-- Keep only the edges appearing on the supplied paths.-/
def mixedSupportGraph (F : DoubleFan G Z H) (L : IndexedLinkage G P) :
    SimpleGraph V :=
  G.deleteEdges (G.edgeSet \ mixedUsedEdges F L)

/--
@isnad1 id=le.0h8v.s6.c6ffda517f41 from=translated src=- shape=911ed454 vocab=ca77425b
-/
theorem mixedSupportGraph_le
    (F : DoubleFan G Z H) (L : IndexedLinkage G P) :
    mixedSupportGraph F L ≤ G :=
  SimpleGraph.deleteEdges_le _

/-- Every proxy-fan path remains a path in the support graph.-/
def DoubleFan.toMixedSupport
    (F : DoubleFan G Z H) (L : IndexedLinkage G P) :
    DoubleFan (mixedSupportGraph F L) Z H := by
  classical
  let lift (slot : Z × Fin 2) :
      (mixedSupportGraph F L).Path slot.1.1 (F.finish slot) := by
    let p := (F.path slot : G.Walk slot.1.1 (F.finish slot))
    have hp : ∀ e ∈ p.edges, e ∈ (mixedSupportGraph F L).edgeSet := by
      intro e he
      simp only [mixedSupportGraph, SimpleGraph.edgeSet_deleteEdges]
      refine ⟨p.edges_subset_edgeSet he, ?_⟩
      intro hdel
      exact hdel.2 (Or.inl ⟨slot,he⟩)
    exact ⟨p.transfer (mixedSupportGraph F L) hp,
      SimpleGraph.Walk.IsPath.transfer hp (F.path slot).property⟩
  have hsupp (slot : Z × Fin 2) :
      pathVertexSet (lift slot) = pathVertexSet (F.path slot) := by
    ext v
    simp [lift, pathVertexSet, SimpleGraph.Walk.support_transfer]
  exact {
    finish := F.finish
    path := lift
    finish_mem := F.finish_mem
    source_only := by
      intro slot v hv hvZ
      rw [hsupp] at hv
      exact F.source_only slot v hv hvZ
    disjoint_outside := by
      intro slot₁ slot₂ hne
      rw [hsupp slot₁, hsupp slot₂]
      exact F.disjoint_outside hne
  }

/-- The residual connector linkage also stays in the support graph.-/
def IndexedLinkage.toMixedSupport
    (F : DoubleFan G Z H) (L : IndexedLinkage G P) :
    IndexedLinkage (mixedSupportGraph F L) P := by
  classical
  let lift (slot : Fin a × Fin 2) :
      (mixedSupportGraph F L).Path (P.start slot) (P.finish slot) := by
    let p := (L.path slot : G.Walk (P.start slot) (P.finish slot))
    have hp : ∀ e ∈ p.edges, e ∈ (mixedSupportGraph F L).edgeSet := by
      intro e he
      simp only [mixedSupportGraph, SimpleGraph.edgeSet_deleteEdges]
      refine ⟨p.edges_subset_edgeSet he, ?_⟩
      intro hdel
      exact hdel.2 (Or.inr ⟨slot,he⟩)
    exact ⟨p.transfer (mixedSupportGraph F L) hp,
      SimpleGraph.Walk.IsPath.transfer hp (L.path slot).property⟩
  have hsupp (slot : Fin a × Fin 2) :
      pathVertexSet (lift slot) = pathVertexSet (L.path slot) := by
    ext v
    simp [lift, pathVertexSet, SimpleGraph.Walk.support_transfer]
  exact {
    path := lift
    disjoint := by
      intro slot₁ slot₂ hne
      rw [hsupp slot₁, hsupp slot₂]
      exact L.disjoint hne
  }

end Woven
end HadwigerLean
