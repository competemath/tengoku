import Tengoku.Erdos64.Erdos64.PentagramEarHull

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

namespace PentagramEarHull

variable {V : Type u} {G : SimpleGraph V}

/-- Explicit incidence-to-route data.  The support condition records the
hull incidence separately; disjointness from the connector is derived below.-/
structure IncidenceBridgeWitness (H : PentagramEarHull G) (i j : Fin 5)
    (K : Connector H i j) where
  route : G.Walk (bVertex H i) (bVertex H j)
  route_isPath : route.IsPath
  route_length : route.length + K.path.length = 8
  route_support_hull : ∀ v, v ∈ route.support → v ∈ hull H

private theorem mem_interior_of_mem_tail_ne_end
    {u v : V} {p : G.Walk u v} {x : V}
    (hx : x ∈ p.support.tail) (hxv : x ≠ v) :
    x ∈ p.support.tail.dropLast := by
  apply List.mem_dropLast_of_mem_of_ne_getLast hx
  grind [p.getLast_support]

private theorem snd_ne_end_of_isPath_of_two_le
    {u v : V} {p : G.Walk u v} (hp : p.IsPath)
    (hlen : 2 ≤ p.length) : p.snd ≠ v := by
  intro hb
  have hnil : ¬ p.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    omega
  have hnodup := hp.support_nodup
  have h1 : 1 < p.support.length := by
    simp [p.length_support]
    omega
  have hl : p.length < p.support.length := by
    simp [p.length_support]
  have heq : p.support[1]'h1 = p.support[p.length]'hl := by
    rw [← p.snd_eq_support_getElem_one hnil]
    have hlast : p.support[p.length]'hl = v := p.support_getElem_length
    exact hb.trans hlast.symm
  have hidx := (List.Nodup.getElem_inj_iff hnodup).mp heq
  omega

private theorem snd_eq_end_of_length_one
    {u v : V} {p : G.Walk u v} (h : p.length = 1) :
    p.snd = v := by
  have hnil : ¬ p.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    omega
  have h1 : 1 < p.support.length := by
    simp [p.length_support, h]
  rw [p.snd_eq_support_getElem_one hnil]
  have hlast : p.support[1]'h1 = v := by
    simpa [h] using p.support_getElem_length
  exact hlast

private theorem snd_not_hull_of_length_ge_two
    (H : PentagramEarHull G) (K : Connector H i j)
    (hlen : 2 ≤ K.path.length) : K.path.snd ∉ hull H := by
  intro hsnd
  have hne : K.path.snd ≠ bVertex H j :=
    snd_ne_end_of_isPath_of_two_le K.isPath hlen
  have hnil : ¬ K.path.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    omega
  have hinter : K.path.snd ∈ K.path.support.tail.dropLast :=
    mem_interior_of_mem_tail_ne_end
      (K.path.snd_mem_tail_support hnil) hne
  exact K.interior_disjoint _ hinter hsnd

private theorem route_snd_ne_end
    {u v : V} {p : G.Walk u v} (hp : p.IsPath)
    (hlen : 2 ≤ p.length) : p.snd ≠ v :=
  snd_ne_end_of_isPath_of_two_le hp hlen

/-- Convert explicit hull-incidence route data into the certified return
interface.  Connector-route disjointness and first-step separation are proved
from the witness support condition and connector interior avoidance.-/
def IncidenceBridgeWitness.toHullReturn
    (H : PentagramEarHull G) (i j : Fin 5) (K : Connector H i j)
    (W : IncidenceBridgeWitness H i j K) : HullReturn H i j K := by
  have hroute := W.route_length
  have hKle : K.path.length ≤ 3 := by
    rcases K.length_one_to_three with h | h | h <;> omega
  have hroute_ge_two : 2 ≤ W.route.length := by
    omega
  have hroute_snd_ne_end : W.route.snd ≠ bVertex H j :=
    route_snd_ne_end W.route_isPath hroute_ge_two
  have hroute_non_nil : ¬ W.route.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    omega
  have hroute_snd_hull : W.route.snd ∈ hull H := by
    apply W.route_support_hull
    exact List.mem_of_mem_tail (W.route.snd_mem_tail_support hroute_non_nil)
  have hfirst : K.path.snd ≠ W.route.snd := by
    rcases K.length_one_to_three with h | h | h
    · intro heq
      apply hroute_snd_ne_end
      exact (snd_eq_end_of_length_one h).symm.trans heq |>.symm
    · intro heq
      exact snd_not_hull_of_length_ge_two H K (by omega)
        (heq.symm ▸ hroute_snd_hull)
    · intro heq
      exact snd_not_hull_of_length_ge_two H K (by omega)
        (heq.symm ▸ hroute_snd_hull)
  have hdisjoint :
      (K.path.take K.path.length).support.tail.Disjoint
        (W.route.take W.route.length).reverse.support.tail := by
    have hend : bVertex H j ∉ W.route.reverse.support.tail := by
      have hnodup :
          (bVertex H j :: W.route.reverse.support.tail).Nodup := by
        rw [W.route.reverse.cons_tail_support]
        exact W.route_isPath.reverse.support_nodup
      exact (List.nodup_cons.mp hnodup).1
    rw [K.path.take_of_length_le (Nat.le_refl _),
      W.route.take_of_length_le (Nat.le_refl _)]
    simp only [SimpleGraph.Walk.support_copy]
    apply List.disjoint_left.2
    intro v hvK hvR
    have hvR0 : v ∈ W.route.reverse.support.tail := by
      simpa only [SimpleGraph.Walk.support_reverse,
        SimpleGraph.Walk.support_copy] using hvR
    have hvj : v ≠ bVertex H j := by
      intro hv
      exact hend (hv ▸ hvR0)
    have hvroute : v ∈ W.route.support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using
        (List.mem_of_mem_tail hvR0)
    exact K.interior_disjoint v
      (mem_interior_of_mem_tail_ne_end hvK hvj)
      (W.route_support_hull v hvroute)
  exact {
    route := W.route
    route_isPath := W.route_isPath
    route_length := W.route_length
    route_disjoint := hdisjoint
    first_steps_distinct := hfirst }

theorem cycle8_of_incidence_bridge_witness
    (H : PentagramEarHull G) (i j : Fin 5) (K : Connector H i j)
    (W : IncidenceBridgeWitness H i j K) :
    ∃ c : G.Walk (bVertex H i) (bVertex H i),
      c.IsCycle ∧ c.length = 8 := by
  exact cycle8_of_hull_return (G := G) H i j K
    (IncidenceBridgeWitness.toHullReturn H i j K W)

end PentagramEarHull

end Erdos64
