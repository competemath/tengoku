import Tengoku.Erdos64.Erdos64.PentagramEarHull
import Tengoku.Erdos64.Erdos64.PentagramEarHullOneCaseProof

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

namespace PentagramEarHull

variable {V : Type u} {G : SimpleGraph V}

private theorem connector_length_three_interior
    (H : PentagramEarHull G) (K : Connector H 0 1)
    (hK : K.path.length = 3) {v : V}
    (hv : v ∈ K.path.support.tail) (hv1 : v ≠ bVertex H 1) :
    v ∈ K.path.support.tail.dropLast := by
  apply List.mem_dropLast_of_mem_of_ne_getLast hv
  grind [K.path.length_support, K.path.getLast_support]

private theorem connector_length_three_not_first_hull
    (H : PentagramEarHull G) (K : Connector H 0 1)
    (hK : K.path.length = 3) :
    K.path.snd ≠ aVertex H 0 := by
  intro h
  have hnil : ¬ K.path.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    omega
  have hnodup := K.isPath.support_nodup
  have h1 : 1 < K.path.support.length := by
    simp [K.path.length_support, hK]
  have h3 : 3 < K.path.support.length := by
    simp [K.path.length_support, hK]
  have hne_b : K.path.snd ≠ bVertex H 1 := by
    intro hb
    have heq : K.path.support[1]'h1 = K.path.support[3]'h3 := by
      rw [← K.path.snd_eq_support_getElem_one hnil]
      have hlast : K.path.support[3]'h3 = bVertex H 1 := by
        simpa [hK] using K.path.support_getElem_length
      exact hb.trans hlast.symm
    have hidx := (List.Nodup.getElem_inj_iff hnodup).mp heq
    omega
  have hsnd : K.path.snd ∈ K.path.support.tail := K.path.snd_mem_tail_support hnil
  have hinter : K.path.snd ∈ K.path.support.tail.dropLast :=
    connector_length_three_interior H K hK hsnd hne_b
  exact K.interior_disjoint _ hinter (by
    rw [h]
    exact Set.mem_union_left _ (Set.mem_union_right _ ⟨0, rfl⟩))

def hullReturn_of_connector_01_length_three
    (H : PentagramEarHull G) (K : Connector H 0 1)
    (hK : K.path.length = 3) : HullReturn H 0 1 K := by
  let route := H.oneCaseProofRoute
  have hroute_path : route.IsPath := by
    simpa [route] using oneCaseProofRoute_isPath H
  have hroute_len : route.length = 5 := by
    simpa [route] using oneCaseProofRoute_length H
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
      simp [route, oneCaseProofRoute, hull, cVertex, aVertex, bVertex] at hvR' ⊢
      aesop
    have hv1 : v ≠ bVertex H 1 := by
      intro hv1
      subst v
      simp [route, oneCaseProofRoute, cVertex, aVertex, bVertex] at hvR
      rcases hvR with h | h | h | h | h <;>
        have hi := H.vertex_injective h <;> simp_all
    exact K.interior_disjoint v
      (connector_length_three_interior H K hK hvK hv1) hvh
  have hfirst : K.path.snd ≠ route.snd := by
    intro h
    apply connector_length_three_not_first_hull H K hK
    change K.path.snd = aVertex H 0 at h
    exact h
  exact {
    route := route
    route_isPath := hroute_path
    route_length := by omega
    route_disjoint := hroute_disjoint
    first_steps_distinct := hfirst }

theorem cycle8_of_connector_01_length_three
    (H : PentagramEarHull G) (K : Connector H 0 1)
    (hK : K.path.length = 3) :
    ∃ c : G.Walk (bVertex H 0) (bVertex H 0),
      c.IsCycle ∧ c.length = 8 := by
  exact cycle8_of_hull_return H 0 1 K
    (hullReturn_of_connector_01_length_three H K hK)

end PentagramEarHull

end Erdos64
