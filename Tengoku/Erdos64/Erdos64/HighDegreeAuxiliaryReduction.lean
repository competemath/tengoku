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
Ducoffe--Dumitru, arXiv:2609.28594v1, Lemma 3.5.
@isnad1 id=ex.2h3v.s7.fcb19da2d49d from=translated src=- shape=d3a9a829 vocab=935eba2f
-/
theorem EdgeMinimalCounterexample.highDegreeAuxGraph_low_internal_degree
    (M : EdgeMinimalCounterexample G)
    (S : Finset (HighDegreeVertex G)) (hS : S.Nonempty) :
    ∃ w ∈ S, internalDegree (highDegreeAuxGraph G) S w ≤ 2 :=
  M.vertexMinimal.twoStep_has_low_internal_degree M.highDegreeTwoStepEmbedding S hS

/-- The sharp edge bound on the auxiliary graph.
@isnad1 id=le.2h2v.s8.040197acf850 from=translated src=- shape=c04c63c7 vocab=203c66f0
-/
theorem EdgeMinimalCounterexample.highDegreeAuxGraph_edge_bound
    (M : EdgeMinimalCounterexample G)
    (hn : 2 ≤ Fintype.card (HighDegreeVertex G)) :
    (highDegreeAuxGraph G).edgeFinset.card + 3 ≤
      2 * Fintype.card (HighDegreeVertex G) :=
  two_degenerate_edge_bound (highDegreeAuxGraph G)
    M.highDegreeAuxGraph_low_internal_degree hn

/-- There are at most `2h - 3` cubic vertices with two high-degree neighbors
when there are at least two high-degree vertices.
@isnad1 id=le.2h2v.s7.a9c87740fe88 from=translated src=- shape=08adee8a vocab=57ac24b4
-/
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
arXiv:2609.28594v1, Theorem 3.7, in exact integer form.
@isnad1 id=and.1h2v.s8.269cb25036df from=translated src=- shape=87c57551 vocab=a901b6f2
-/
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
