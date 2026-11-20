import Tengoku.Erdos64.Erdos64.PentagramEarHull
import Tengoku.Erdos64.Erdos64.PentagramEarHullCasework

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

namespace PentagramEarHull

variable {V : Type u} {G : SimpleGraph V}

/-- The length-seven route `b0-a0-c0-c1-c2-c3-a3-b3`.-/
def route03LengthOne (H : PentagramEarHull G) :
    G.Walk (bVertex H 0) (bVertex H 3) :=
  SimpleGraph.Walk.cons (H.ab_adj 0).symm <|
    SimpleGraph.Walk.cons (H.ca_adj 0).symm <|
      SimpleGraph.Walk.cons (H.c_adj 0) <|
        SimpleGraph.Walk.cons (H.c_adj 1) <|
          SimpleGraph.Walk.cons (H.c_adj 2) <|
            SimpleGraph.Walk.cons (H.ca_adj 3) <|
              SimpleGraph.Walk.cons (H.ab_adj 3) .nil

/-- The length-six route `b0-a0-c0-c4-c3-a3-b3`.-/
def route03LengthTwo (H : PentagramEarHull G) :
    G.Walk (bVertex H 0) (bVertex H 3) :=
  SimpleGraph.Walk.cons (H.ab_adj 0).symm <|
    SimpleGraph.Walk.cons (H.ca_adj 0).symm <|
      SimpleGraph.Walk.cons (H.c_adj 4).symm <|
        SimpleGraph.Walk.cons (H.c_adj 3).symm <|
          SimpleGraph.Walk.cons (H.ca_adj 3) <|
            SimpleGraph.Walk.cons (H.ab_adj 3) .nil

/--
@isnad1 id=eq.0h3v.s5.c598964ca7aa from=translated src=- shape=990c9dfd vocab=83cd0264
-/
theorem route03LengthOne_length (H : PentagramEarHull G) :
    H.route03LengthOne.length = 7 := by
  rfl

/--
@isnad1 id=eq.0h3v.s5.73d5b81844e7 from=translated src=- shape=990c9dfd vocab=eb166df4
-/
theorem route03LengthTwo_length (H : PentagramEarHull G) :
    H.route03LengthTwo.length = 6 := by
  rfl

/--
@isnad1 id=ispath.0h3v.s5.21a1ad6e7a6e from=translated src=- shape=def4ed68 vocab=03482578
-/
theorem route03LengthOne_isPath (H : PentagramEarHull G) :
    H.route03LengthOne.IsPath := by
  apply (SimpleGraph.Walk.isPath_def _).mpr
  change List.Nodup
    [H.vertex (.inr (.inr 0)), H.vertex (.inr (.inl 0)),
      H.vertex (.inl 0), H.vertex (.inl 1), H.vertex (.inl 2),
      H.vertex (.inl 3), H.vertex (.inr (.inl 3)),
      H.vertex (.inr (.inr 3))]
  have hxs : ([.inr (.inr 0), .inr (.inl 0), .inl 0, .inl 1,
      .inl 2, .inl 3, .inr (.inl 3), .inr (.inr 3)] :
      List (Sum (Fin 5) (Sum (Fin 5) (Fin 5)))).Nodup := by decide
  exact List.Nodup.map H.vertex_injective hxs

/--
@isnad1 id=ispath.0h3v.s5.fca5d2e77b2c from=translated src=- shape=def4ed68 vocab=060ac656
-/
theorem route03LengthTwo_isPath (H : PentagramEarHull G) :
    H.route03LengthTwo.IsPath := by
  apply (SimpleGraph.Walk.isPath_def _).mpr
  change List.Nodup
    [H.vertex (.inr (.inr 0)), H.vertex (.inr (.inl 0)),
      H.vertex (.inl 0), H.vertex (.inl 4), H.vertex (.inl 3),
      H.vertex (.inr (.inl 3)), H.vertex (.inr (.inr 3))]
  have hxs : ([.inr (.inr 0), .inr (.inl 0), .inl 0, .inl 4,
      .inl 3, .inr (.inl 3), .inr (.inr 3)] :
      List (Sum (Fin 5) (Sum (Fin 5) (Fin 5)))).Nodup := by decide
  exact List.Nodup.map H.vertex_injective hxs

private theorem connector03_tail_interior
    (H : PentagramEarHull G) (K : Connector H 0 3) {v : V}
    (hv : v ∈ K.path.support.tail) (hv3 : v ≠ bVertex H 3) :
    v ∈ K.path.support.tail.dropLast := by
  apply List.mem_dropLast_of_mem_of_ne_getLast hv
  grind [K.path.getLast_support]

private theorem connector03_snd_ne_a0
    (H : PentagramEarHull G) (K : Connector H 0 3) :
    K.path.snd ≠ aVertex H 0 := by
  intro h
  have hnil : ¬ K.path.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    rcases K.length_one_to_three with hlen | hlen | hlen <;> omega
  have hne : K.path.snd ≠ bVertex H 3 := by
    intro he
    have hi := H.vertex_injective (h.symm.trans he)
    simp at hi
  have hinter := connector03_tail_interior H K
    (K.path.snd_mem_tail_support hnil) hne
  apply K.interior_disjoint _ hinter
  rw [h]
  exact Set.mem_union_left _ (Set.mem_union_right _ ⟨0, rfl⟩)

private theorem connector03_route_disjoint
    (H : PentagramEarHull G) (K : Connector H 0 3)
    (route : G.Walk (bVertex H 0) (bVertex H 3))
    (hroute : route.IsPath)
    (hsupp : ∀ v, v ∈ route.support → v ∈ hull H) :
    (K.path.take K.path.length).support.tail.Disjoint
      (route.take route.length).reverse.support.tail := by
  have hend : bVertex H 3 ∉ route.reverse.support.tail := by
    have hnodup : (bVertex H 3 :: route.reverse.support.tail).Nodup := by
      rw [route.reverse.cons_tail_support]
      exact hroute.reverse.support_nodup
    exact (List.nodup_cons.mp hnodup).1
  rw [K.path.take_of_length_le (Nat.le_refl _),
    route.take_of_length_le (Nat.le_refl _)]
  simp only [SimpleGraph.Walk.support_copy]
  apply List.disjoint_left.2
  intro v hvK hvR
  have hvR0 : v ∈ route.reverse.support.tail := by
    simpa only [SimpleGraph.Walk.support_reverse,
      SimpleGraph.Walk.support_copy] using hvR
  have hv3 : v ≠ bVertex H 3 := by
    intro hv
    exact hend (hv ▸ hvR0)
  have hvroute : v ∈ route.support := by
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using
      (List.mem_of_mem_tail hvR0)
  exact K.interior_disjoint v
    (connector03_tail_interior H K hvK hv3) (hsupp v hvroute)

/-- The normalized `(0,3)` length-one connector closes along the explicit
length-seven hull route.-/
def hullReturn_of_connector_03_length_one
    (H : PentagramEarHull G) (K : Connector H 0 3)
    (hK : K.path.length = 1) : HullReturn H 0 3 K := by
  refine {
    route := H.route03LengthOne
    route_isPath := route03LengthOne_isPath H
    route_length := by rw [route03LengthOne_length, hK]
    route_disjoint := ?_
    first_steps_distinct := ?_ }
  · apply connector03_route_disjoint H K H.route03LengthOne
      (route03LengthOne_isPath H)
    intro v hv
    simp [route03LengthOne, hull, cVertex, aVertex, bVertex] at hv ⊢
    aesop
  · change K.path.snd ≠ aVertex H 0
    exact connector03_snd_ne_a0 H K

/-- The normalized `(0,3)` length-two connector closes along the explicit
length-six hull route.-/
def hullReturn_of_connector_03_length_two
    (H : PentagramEarHull G) (K : Connector H 0 3)
    (hK : K.path.length = 2) : HullReturn H 0 3 K := by
  refine {
    route := H.route03LengthTwo
    route_isPath := route03LengthTwo_isPath H
    route_length := by rw [route03LengthTwo_length, hK]
    route_disjoint := ?_
    first_steps_distinct := ?_ }
  · apply connector03_route_disjoint H K H.route03LengthTwo
      (route03LengthTwo_isPath H)
    intro v hv
    simp [route03LengthTwo, hull, cVertex, aVertex, bVertex] at hv ⊢
    aesop
  · change K.path.snd ≠ aVertex H 0
    exact connector03_snd_ne_a0 H K

/--
@isnad1 id=ex.1h4v.s8.e2f6e69e44f5 from=translated src=- shape=19edbc8a vocab=3b04f5d3
-/
theorem cycle8_of_connector_03_length_one
    (H : PentagramEarHull G) (K : Connector H 0 3)
    (hK : K.path.length = 1) :
    ∃ c : G.Walk (bVertex H 0) (bVertex H 0),
      c.IsCycle ∧ c.length = 8 := by
  exact cycle8_of_hull_return H 0 3 K
    (hullReturn_of_connector_03_length_one H K hK)

/--
@isnad1 id=ex.1h4v.s8.e2ead618c013 from=translated src=- shape=19edbc8a vocab=3b04f5d3
-/
theorem cycle8_of_connector_03_length_two
    (H : PentagramEarHull G) (K : Connector H 0 3)
    (hK : K.path.length = 2) :
    ∃ c : G.Walk (bVertex H 0) (bVertex H 0),
      c.IsCycle ∧ c.length = 8 := by
  exact cycle8_of_hull_return H 0 3 K
    (hullReturn_of_connector_03_length_two H K hK)

end PentagramEarHull

end Erdos64
