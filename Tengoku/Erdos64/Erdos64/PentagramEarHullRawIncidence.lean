import Tengoku.Erdos64.Erdos64.PentagramEarHullIncidenceBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

namespace PentagramEarHull

variable {V : Type u} {G : SimpleGraph V}

private def rawRoute01LengthOne (H : PentagramEarHull G) :
    G.Walk (bVertex H 0) (bVertex H 1) :=
  SimpleGraph.Walk.cons (H.ab_adj 0).symm <|
    SimpleGraph.Walk.cons (H.ca_adj 0).symm <|
      SimpleGraph.Walk.cons (H.c_adj 0) <|
        SimpleGraph.Walk.cons (H.c_adj 1) <|
          SimpleGraph.Walk.cons (H.c_adj 2) <|
            SimpleGraph.Walk.cons (H.ca_adj 3) <|
              SimpleGraph.Walk.cons (H.shifted_ab_adj 1) .nil

private def rawRoute01LengthTwo (H : PentagramEarHull G) :
    G.Walk (bVertex H 0) (bVertex H 1) :=
  SimpleGraph.Walk.cons (H.ab_adj 0).symm <|
    SimpleGraph.Walk.cons (H.ca_adj 0).symm <|
      SimpleGraph.Walk.cons (H.c_adj 4).symm <|
        SimpleGraph.Walk.cons (H.c_adj 3).symm <|
          SimpleGraph.Walk.cons (H.ca_adj 3) <|
            SimpleGraph.Walk.cons (H.shifted_ab_adj 1) .nil

private def rawRoute01LengthThree (H : PentagramEarHull G) :
    G.Walk (bVertex H 0) (bVertex H 1) :=
  SimpleGraph.Walk.cons (H.ab_adj 0).symm <|
    SimpleGraph.Walk.cons (H.ca_adj 0).symm <|
      SimpleGraph.Walk.cons (H.c_adj 0) <|
        SimpleGraph.Walk.cons (H.ca_adj 1) <|
          SimpleGraph.Walk.cons (H.ab_adj 1) .nil

private theorem rawRoute01LengthOne_isPath (H : PentagramEarHull G) :
    (rawRoute01LengthOne H).IsPath := by
  apply (SimpleGraph.Walk.isPath_def _).mpr
  change List.Nodup
    [H.vertex (.inr (.inr 0)), H.vertex (.inr (.inl 0)),
      H.vertex (.inl 0), H.vertex (.inl 1), H.vertex (.inl 2),
      H.vertex (.inl 3), H.vertex (.inr (.inl 3)),
      H.vertex (.inr (.inr 1))]
  have hxs : ([.inr (.inr 0), .inr (.inl 0), .inl 0, .inl 1,
      .inl 2, .inl 3, .inr (.inl 3), .inr (.inr 1)] :
      List (Sum (Fin 5) (Sum (Fin 5) (Fin 5)))).Nodup := by decide
  exact List.Nodup.map H.vertex_injective hxs

private theorem rawRoute01LengthTwo_isPath (H : PentagramEarHull G) :
    (rawRoute01LengthTwo H).IsPath := by
  apply (SimpleGraph.Walk.isPath_def _).mpr
  change List.Nodup
    [H.vertex (.inr (.inr 0)), H.vertex (.inr (.inl 0)),
      H.vertex (.inl 0), H.vertex (.inl 4), H.vertex (.inl 3),
      H.vertex (.inr (.inl 3)), H.vertex (.inr (.inr 1))]
  have hxs : ([.inr (.inr 0), .inr (.inl 0), .inl 0, .inl 4,
      .inl 3, .inr (.inl 3), .inr (.inr 1)] :
      List (Sum (Fin 5) (Sum (Fin 5) (Fin 5)))).Nodup := by decide
  exact List.Nodup.map H.vertex_injective hxs

private theorem rawRoute01LengthThree_isPath (H : PentagramEarHull G) :
    (rawRoute01LengthThree H).IsPath := by
  apply (SimpleGraph.Walk.isPath_def _).mpr
  change List.Nodup
    [H.vertex (.inr (.inr 0)), H.vertex (.inr (.inl 0)),
      H.vertex (.inl 0), H.vertex (.inl 1),
      H.vertex (.inr (.inl 1)), H.vertex (.inr (.inr 1))]
  have hxs : ([.inr (.inr 0), .inr (.inl 0), .inl 0, .inl 1,
      .inr (.inl 1), .inr (.inr 1)] :
      List (Sum (Fin 5) (Sum (Fin 5) (Fin 5)))).Nodup := by decide
  exact List.Nodup.map H.vertex_injective hxs

private theorem rawRoute01LengthOne_support_hull (H : PentagramEarHull G) :
    ∀ v, v ∈ (rawRoute01LengthOne H).support → v ∈ hull H := by
  intro v hv
  simp [rawRoute01LengthOne, hull, cVertex, aVertex, bVertex] at hv ⊢
  aesop

private theorem rawRoute01LengthTwo_support_hull (H : PentagramEarHull G) :
    ∀ v, v ∈ (rawRoute01LengthTwo H).support → v ∈ hull H := by
  intro v hv
  simp [rawRoute01LengthTwo, hull, cVertex, aVertex, bVertex] at hv ⊢
  aesop

private theorem rawRoute01LengthThree_support_hull (H : PentagramEarHull G) :
    ∀ v, v ∈ (rawRoute01LengthThree H).support → v ∈ hull H := by
  intro v hv
  simp [rawRoute01LengthThree, hull, cVertex, aVertex, bVertex] at hv ⊢
  aesop

/-- Every existing `(0,1)` connector supplies an explicit hull-incidence
route, with the route selected by its certified length.-/
def incidenceBridgeWitness_of_connector_01
    (H : PentagramEarHull G) (K : Connector H 0 1)
    (hK : K.path.length = 1 ∨ K.path.length = 2 ∨ K.path.length = 3) :
    IncidenceBridgeWitness H 0 1 K := by
  by_cases hK1 : K.path.length = 1
  · exact {
      route := rawRoute01LengthOne H
      route_isPath := rawRoute01LengthOne_isPath H
      route_length := by rw [show (rawRoute01LengthOne H).length = 7 by rfl, hK1]
      route_support_hull := rawRoute01LengthOne_support_hull H }
  by_cases hK2 : K.path.length = 2
  · exact {
      route := rawRoute01LengthTwo H
      route_isPath := rawRoute01LengthTwo_isPath H
      route_length := by rw [show (rawRoute01LengthTwo H).length = 6 by rfl, hK2]
      route_support_hull := rawRoute01LengthTwo_support_hull H }
  have hK3 : K.path.length = 3 := by
    rcases hK with h | h | h
    · exact (hK1 h).elim
    · exact (hK2 h).elim
    · exact h
  exact {
      route := rawRoute01LengthThree H
      route_isPath := rawRoute01LengthThree_isPath H
      route_length := by rw [show (rawRoute01LengthThree H).length = 5 by rfl, hK3]
      route_support_hull := rawRoute01LengthThree_support_hull H }

/--
@isnad1 id=ex.1h4v.s8.2bef9c6060d3 from=translated src=- shape=d135db9b vocab=3b04f5d3
-/
theorem cycle8_of_raw_incidence_connector_01
    (H : PentagramEarHull G) (K : Connector H 0 1)
    (hK : K.path.length = 1 ∨ K.path.length = 2 ∨ K.path.length = 3) :
    ∃ c : G.Walk (bVertex H 0) (bVertex H 0),
      c.IsCycle ∧ c.length = 8 := by
  exact cycle8_of_incidence_bridge_witness H 0 1 K
    (incidenceBridgeWitness_of_connector_01 H K hK)

end PentagramEarHull

end Erdos64
