import Tengoku.Erdos64.Erdos64.HighDegreeAuxiliary
import Tengoku.Erdos64.Erdos64.SmallerTwoStepReduction
import Tengoku.Erdos64.Erdos64.CubicDensityFromConnectors

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Every nonempty induced part of the high-degree auxiliary graph has an
internal vertex degree at most two. This is the degeneracy conclusion of
Ducoffe--Dumitru, arXiv:2609.28594v1, Lemma 3.5.-/
theorem EdgeMinimalCounterexample.highDegreeAuxGraph_low_internal_degree
    (M : EdgeMinimalCounterexample G)
    (S : Finset (HighDegreeVertex G)) (hS : S.Nonempty) :
    ∃ w ∈ S, internalDegree (highDegreeAuxGraph G) S w ≤ 2 :=
  M.vertexMinimal.twoStep_has_low_internal_degree M.highDegreeTwoStepEmbedding S hS

/-- The sharp edge bound on the auxiliary graph.-/
theorem EdgeMinimalCounterexample.highDegreeAuxGraph_edge_bound
    (M : EdgeMinimalCounterexample G)
    (hn : 2 ≤ Fintype.card (HighDegreeVertex G)) :
    (highDegreeAuxGraph G).edgeFinset.card + 3 ≤
      2 * Fintype.card (HighDegreeVertex G) :=
  two_degenerate_edge_bound (highDegreeAuxGraph G)
    M.highDegreeAuxGraph_low_internal_degree hn

/-- There are at most `2h - 3` cubic vertices with two high-degree neighbors
when there are at least two high-degree vertices.-/
theorem EdgeMinimalCounterexample.degreeThreeTwoHighNeighbors_card_bound
    (M : EdgeMinimalCounterexample G)
    (hn : 2 ≤ (Finset.univ.filter (fun v => 4 ≤ G.degree v)).card) :
    (degreeThreeTwoHighNeighbors G).card + 3 ≤
      2 * (Finset.univ.filter (fun v => 4 ≤ G.degree v)).card := by
  have hcard : Fintype.card (HighDegreeVertex G) =
      (Finset.univ.filter (fun v => 4 ≤ G.degree v)).card := by
    exact Fintype.card_subtype _
  have hbound := M.highDegreeAuxGraph_edge_bound (by omega)
  rw [← SimpleGraph.card_edgeSet, M.highDegreeAuxGraph_edge_card, hcard] at hbound
  exact hbound

/-- The strengthened cubic-density bound of Ducoffe--Dumitru,
arXiv:2609.28594v1, Theorem 3.7, in exact integer form.-/
theorem EdgeMinimalCounterexample.cubic_density_additive_three
    (M : EdgeMinimalCounterexample G) :
    2 * (Finset.univ.filter (fun v => 4 ≤ G.degree v)).card + 3 ≤
      (Finset.univ.filter (fun v => G.degree v = 3)).card ∧
    2 * Fintype.card V + 3 ≤
      3 * (Finset.univ.filter (fun v => G.degree v = 3)).card := by
  apply M.cubic_density_of_conditional_connector_bound
  dsimp only
  intro hn
  exact M.degreeThreeTwoHighNeighbors_card_bound hn

end Erdos64
