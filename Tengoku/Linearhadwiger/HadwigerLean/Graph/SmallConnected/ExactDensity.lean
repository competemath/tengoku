import Tengoku.Linearhadwiger.HadwigerLean.Graph.CliqueDensity.Reduction
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Deleting surplus edges to achieve an exact integral density
-/

namespace HadwigerLean

universe u

/--
@isnad1 id=ex.1h3v.s5.d064fecd1be1 from=translated src=- shape=4b940873 vocab=c33c6098
-/
theorem exists_spanning_subgraph_exact_edgeCount
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (m : ℕ) (hm : m ≤ edgeCount G) :
    ∃ H : SimpleGraph V, H ≤ G ∧ edgeCount H = m := by
  classical
  obtain ⟨E, hEG, hEcard⟩ :=
    Finset.exists_subset_card_eq
      (s := G.edgeFinset) (n := m)
      (by simpa only [edgeCount_eq_card_edgeFinset] using hm)
  let H := G.deleteEdges ((G.edgeFinset \ E : Finset (Sym2 V)) : Set (Sym2 V))
  have hHedges : H.edgeFinset = E := by
    change (G.deleteEdges ((G.edgeFinset \ E : Finset (Sym2 V)) : Set (Sym2 V))).edgeFinset = E
    rw [G.edgeFinset_deleteEdges]
    exact Finset.sdiff_sdiff_eq_self hEG
  refine ⟨H, G.deleteEdges_le _, ?_⟩
  rw [edgeCount_eq_card_edgeFinset, hHedges]
  exact hEcard

end HadwigerLean
