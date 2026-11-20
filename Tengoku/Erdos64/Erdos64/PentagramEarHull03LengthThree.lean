import Tengoku.Erdos64.Erdos64.PentagramEarHull
import Tengoku.Erdos64.Erdos64.PentagramEarHullCasework

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

namespace PentagramEarHull

variable {V : Type u} {G : SimpleGraph V}

/-- The hull-only route `b0-a2-c2-c3-a3-b3`.-/
def route03 (H : PentagramEarHull G) :
    G.Walk (bVertex H 0) (bVertex H 3) :=
  SimpleGraph.Walk.cons (H.shifted_ab_adj 0).symm <|
    SimpleGraph.Walk.cons (H.ca_adj 2).symm <|
      SimpleGraph.Walk.cons (H.c_adj 2) <|
        SimpleGraph.Walk.cons (H.ca_adj 3) <|
          SimpleGraph.Walk.cons (H.ab_adj 3) .nil

theorem route03_length (H : PentagramEarHull G) :
    (H.route03).length = 5 := by
  rfl

theorem route03_isPath (H : PentagramEarHull G) :
    H.route03.IsPath := by
  apply (SimpleGraph.Walk.isPath_def _).mpr
  change List.Nodup
    [H.vertex (.inr (.inr 0)), H.vertex (.inr (.inl 2)),
      H.vertex (.inl 2), H.vertex (.inl 3),
      H.vertex (.inr (.inl 3)), H.vertex (.inr (.inr 3))]
  let xs : List (Sum (Fin 5) (Sum (Fin 5) (Fin 5))) :=
    [.inr (.inr 0), .inr (.inl 2), .inl 2, .inl 3,
      .inr (.inl 3), .inr (.inr 3)]
  have hxs : xs.Nodup := by
    decide
  exact List.Nodup.map H.vertex_injective hxs

private theorem connector_length_three_interior_03
    (H : PentagramEarHull G) (K : Connector H 0 3)
    (hK : K.path.length = 3) {v : V}
    (hv : v ∈ K.path.support.tail) (hv3 : v ≠ bVertex H 3) :
    v ∈ K.path.support.tail.dropLast := by
  apply List.mem_dropLast_of_mem_of_ne_getLast hv
  grind [K.path.length_support, K.path.getLast_support]

private theorem connector_length_three_not_first_hull_03
    (H : PentagramEarHull G) (K : Connector H 0 3)
    (hK : K.path.length = 3) :
    K.path.snd ≠ aVertex H 2 := by
  intro h
  have hnil : ¬ K.path.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    omega
  have hnodup := K.isPath.support_nodup
  have h1 : 1 < K.path.support.length := by
    simp [K.path.length_support, hK]
  have h3 : 3 < K.path.support.length := by
    simp [K.path.length_support, hK]
  have hne_b : K.path.snd ≠ bVertex H 3 := by
    intro hb
    have heq : K.path.support[1]'h1 = K.path.support[3]'h3 := by
      rw [← K.path.snd_eq_support_getElem_one hnil]
      have hlast : K.path.support[3]'h3 = bVertex H 3 := by
        simpa [hK] using K.path.support_getElem_length
      exact hb.trans hlast.symm
    have hidx := (List.Nodup.getElem_inj_iff hnodup).mp heq
    omega
  have hsnd : K.path.snd ∈ K.path.support.tail :=
    K.path.snd_mem_tail_support hnil
  have hinter : K.path.snd ∈ K.path.support.tail.dropLast :=
    connector_length_three_interior_03 H K hK hsnd hne_b
  exact K.interior_disjoint _ hinter (by
    rw [h]
    exact Set.mem_union_left _ (Set.mem_union_right _ ⟨2, rfl⟩))

/-- The `(0,3)` connector-length-three route satisfies `HullReturn` and closes
to an 8-cycle.-/
def hullReturn_of_connector_03_length_three
    (H : PentagramEarHull G) (K : Connector H 0 3)
    (hK : K.path.length = 3) : HullReturn H 0 3 K := by
  let route := H.route03
  have hroute_path : route.IsPath := by
    simpa [route] using route03_isPath H
  have hroute_len : route.length = 5 := by
    simpa [route] using route03_length H
  have hroute_disjoint :
      (K.path.take K.path.length).support.tail.Disjoint
        (route.take route.length).reverse.support.tail := by
    rw [K.path.take_of_length_le (Nat.le_refl _),
      route.take_of_length_le (Nat.le_refl _)]
    simp only [SimpleGraph.Walk.support_copy]
    apply List.disjoint_left.2
    intro v hvK hvR
    have hvR' : v ∈ route.reverse.support := List.mem_of_mem_tail hvR
    have hvh : v ∈ hull H := by
      simp [route, route03, hull, cVertex, aVertex, bVertex] at hvR' ⊢
      aesop
    have hv3 : v ≠ bVertex H 3 := by
      intro hv3
      subst v
      simp [route, route03, cVertex, aVertex, bVertex] at hvR
      rcases hvR with h | h | h | h | h <;>
        have hi := H.vertex_injective h <;> simp_all
    exact K.interior_disjoint v
      (connector_length_three_interior_03 H K hK hvK hv3) hvh
  have hfirst : K.path.snd ≠ route.snd := by
    intro h
    apply connector_length_three_not_first_hull_03 H K hK
    change K.path.snd = aVertex H 2 at h
    exact h
  exact {
    route := route
    route_isPath := hroute_path
    route_length := by omega
    route_disjoint := hroute_disjoint
    first_steps_distinct := hfirst }

theorem cycle8_of_connector_03_length_three
    (H : PentagramEarHull G) (K : Connector H 0 3)
    (hK : K.path.length = 3) :
    ∃ c : G.Walk (bVertex H 0) (bVertex H 0),
      c.IsCycle ∧ c.length = 8 := by
  exact cycle8_of_hull_return H 0 3 K
    (hullReturn_of_connector_03_length_three H K hK)

end PentagramEarHull

end Erdos64
