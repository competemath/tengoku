import Tengoku.Erdos64.Erdos64.PentagramEarHullOneCaseProof
import Tengoku.Erdos64.Erdos64.PentagramEarHullOneCaseHullReturn

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

namespace PentagramEarHull

variable {V : Type u} {G : SimpleGraph V}

private def routeLengthTwo (H : PentagramEarHull G) :
    G.Walk (bVertex H 0) (bVertex H 1) :=
  SimpleGraph.Walk.cons (H.ab_adj 0).symm <|
    SimpleGraph.Walk.cons (H.ca_adj 0).symm <|
      SimpleGraph.Walk.cons (H.c_adj 4).symm <|
        SimpleGraph.Walk.cons (H.c_adj 3).symm <|
          SimpleGraph.Walk.cons (H.ca_adj 3) <|
            SimpleGraph.Walk.cons (H.shifted_ab_adj 1) .nil

private theorem routeLengthTwo_length (H : PentagramEarHull G) :
    (routeLengthTwo H).length = 6 := by
  rfl

private theorem routeLengthTwo_isPath (H : PentagramEarHull G) :
    (routeLengthTwo H).IsPath := by
  apply (SimpleGraph.Walk.isPath_def _).mpr
  change List.Nodup
    [H.vertex (.inr (.inr 0)), H.vertex (.inr (.inl 0)),
      H.vertex (.inl 0), H.vertex (.inl 4), H.vertex (.inl 3),
      H.vertex (.inr (.inl 3)), H.vertex (.inr (.inr 1))]
  let xs : List (Sum (Fin 5) (Sum (Fin 5) (Fin 5))) :=
    [.inr (.inr 0), .inr (.inl 0), .inl 0, .inl 4, .inl 3,
      .inr (.inl 3), .inr (.inr 1)]
  have hxs : xs.Nodup := by decide
  exact List.Nodup.map H.vertex_injective hxs

private theorem mem_interior_of_mem_tail_ne_end
    {u v : V} {p : G.Walk u v} {x : V}
    (hx : x ∈ p.support.tail) (hxv : x ≠ v) :
    x ∈ p.support.tail.dropLast := by
  apply List.mem_dropLast_of_mem_of_ne_getLast hx
  grind [p.getLast_support]

private theorem length_two_snd_ne_end
    (H : PentagramEarHull G) (K : Connector H 0 1)
    (hK : K.path.length = 2) : K.path.snd ≠ bVertex H 1 := by
  intro hb
  have hnil : ¬ K.path.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    omega
  have hnodup := K.isPath.support_nodup
  have h1 : 1 < K.path.support.length := by
    simp [K.path.length_support, hK]
  have h2 : 2 < K.path.support.length := by
    simp [K.path.length_support, hK]
  have heq : K.path.support[1]'h1 = K.path.support[2]'h2 := by
    rw [← K.path.snd_eq_support_getElem_one hnil]
    have hlast : K.path.support[2]'h2 = bVertex H 1 := by
      simpa [hK] using K.path.support_getElem_length
    exact hb.trans hlast.symm
  have hidx := (List.Nodup.getElem_inj_iff hnodup).mp heq
  omega

private theorem length_two_snd_ne_first_hull
    (H : PentagramEarHull G) (K : Connector H 0 1)
    (hK : K.path.length = 2) : K.path.snd ≠ aVertex H 0 := by
  intro h
  have hnil : ¬ K.path.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    omega
  have hsnd : K.path.snd ∈ K.path.support.tail := K.path.snd_mem_tail_support hnil
  have hinter : K.path.snd ∈ K.path.support.tail.dropLast :=
    mem_interior_of_mem_tail_ne_end hsnd (length_two_snd_ne_end H K hK)
  exact K.interior_disjoint _ hinter (by
    rw [h]
    exact Set.mem_union_left _ (Set.mem_union_right _ ⟨0, rfl⟩))

private theorem routeLengthTwo_disjoint
    (H : PentagramEarHull G) (K : Connector H 0 1)
    (hK : K.path.length = 2) :
    (K.path.take K.path.length).support.tail.Disjoint
      (routeLengthTwo H).reverse.support.tail := by
  rw [K.path.take_of_length_le (Nat.le_refl _)]
  simp only [SimpleGraph.Walk.support_copy]
  apply List.disjoint_left.2
  intro v hvK hvR
  have hvR' : v ∈ (routeLengthTwo H).reverse.support :=
    List.mem_of_mem_tail hvR
  have hvh : v ∈ hull H := by
    simp [routeLengthTwo, hull, cVertex, aVertex, bVertex] at hvR' ⊢
    aesop
  have hv1 : v ≠ bVertex H 1 := by
    intro hv1
    subst v
    simp [routeLengthTwo, aVertex, bVertex, cVertex] at hvR
    rcases hvR with h | h | h | h | h | h <;>
      have hi := H.vertex_injective h <;> simp_all
  exact K.interior_disjoint v
    (mem_interior_of_mem_tail_ne_end hvK hv1) hvh

def hullReturn_of_connector_01_length_two
    (H : PentagramEarHull G) (K : Connector H 0 1)
    (hK : K.path.length = 2) : HullReturn H 0 1 K := by
  have hroute_path := routeLengthTwo_isPath H
  have hroute_len := routeLengthTwo_length H
  have hfirst : K.path.snd ≠ (routeLengthTwo H).snd := by
    intro h
    apply length_two_snd_ne_first_hull H K hK
    change K.path.snd = aVertex H 0 at h
    exact h
  exact {
    route := routeLengthTwo H
    route_isPath := hroute_path
    route_length := by omega
    route_disjoint := routeLengthTwo_disjoint H K hK
    first_steps_distinct := hfirst }

/--
@isnad1 id=ex.1h4v.s8.df04d52099de from=translated src=- shape=19edbc8a vocab=3b04f5d3
-/
theorem cycle8_of_connector_01_length_two
    (H : PentagramEarHull G) (K : Connector H 0 1)
    (hK : K.path.length = 2) :
    ∃ c : G.Walk (bVertex H 0) (bVertex H 0),
      c.IsCycle ∧ c.length = 8 := by
  exact cycle8_of_hull_return H 0 1 K
    (hullReturn_of_connector_01_length_two H K hK)

private def routeLengthOne (H : PentagramEarHull G) :
    G.Walk (bVertex H 0) (bVertex H 1) :=
  SimpleGraph.Walk.cons (H.ab_adj 0).symm <|
    SimpleGraph.Walk.cons (H.ca_adj 0).symm <|
      SimpleGraph.Walk.cons (H.c_adj 0) <|
        SimpleGraph.Walk.cons (H.c_adj 1) <|
          SimpleGraph.Walk.cons (H.c_adj 2) <|
            SimpleGraph.Walk.cons (H.ca_adj 3) <|
              SimpleGraph.Walk.cons (H.shifted_ab_adj 1) .nil

private theorem routeLengthOne_length (H : PentagramEarHull G) :
    (routeLengthOne H).length = 7 := by
  rfl

private theorem routeLengthOne_isPath (H : PentagramEarHull G) :
    (routeLengthOne H).IsPath := by
  apply (SimpleGraph.Walk.isPath_def _).mpr
  change List.Nodup
    [H.vertex (.inr (.inr 0)), H.vertex (.inr (.inl 0)),
      H.vertex (.inl 0), H.vertex (.inl 1), H.vertex (.inl 2),
      H.vertex (.inl 3), H.vertex (.inr (.inl 3)),
      H.vertex (.inr (.inr 1))]
  let xs : List (Sum (Fin 5) (Sum (Fin 5) (Fin 5))) :=
    [.inr (.inr 0), .inr (.inl 0), .inl 0, .inl 1, .inl 2,
      .inl 3, .inr (.inl 3), .inr (.inr 1)]
  have hxs : xs.Nodup := by decide
  exact List.Nodup.map H.vertex_injective hxs

private theorem length_one_snd_eq_end
    (H : PentagramEarHull G) (K : Connector H 0 1)
    (hK : K.path.length = 1) : K.path.snd = bVertex H 1 := by
  have hnil : ¬ K.path.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    omega
  have h1 : 1 < K.path.support.length := by
    simp [K.path.length_support, hK]
  rw [K.path.snd_eq_support_getElem_one hnil]
  have hlast : K.path.support[1]'h1 = bVertex H 1 := by
    simpa [hK] using K.path.support_getElem_length
  exact hlast

private theorem routeLengthOne_disjoint
    (H : PentagramEarHull G) (K : Connector H 0 1)
    (hK : K.path.length = 1) :
    (K.path.take K.path.length).support.tail.Disjoint
      (routeLengthOne H).reverse.support.tail := by
  rw [K.path.take_of_length_le (Nat.le_refl _)]
  simp only [SimpleGraph.Walk.support_copy]
  apply List.disjoint_left.2
  intro v hvK hvR
  have hvR' : v ∈ (routeLengthOne H).reverse.support :=
    List.mem_of_mem_tail hvR
  have hvh : v ∈ hull H := by
    simp [routeLengthOne, hull, cVertex, aVertex, bVertex] at hvR' ⊢
    aesop
  have hv1 : v ≠ bVertex H 1 := by
    intro hv1
    subst v
    simp [routeLengthOne, aVertex, bVertex, cVertex] at hvR
    rcases hvR with h | h | h | h | h | h | h <;>
      have hi := H.vertex_injective h <;> simp_all
  exact K.interior_disjoint v
    (mem_interior_of_mem_tail_ne_end hvK hv1) hvh

def hullReturn_of_connector_01_length_one
    (H : PentagramEarHull G) (K : Connector H 0 1)
    (hK : K.path.length = 1) : HullReturn H 0 1 K := by
  have hroute_path := routeLengthOne_isPath H
  have hroute_len := routeLengthOne_length H
  have hfirst : K.path.snd ≠ (routeLengthOne H).snd := by
    intro h
    have hb : K.path.snd = bVertex H 1 := length_one_snd_eq_end H K hK
    have hv : bVertex H 1 = aVertex H 0 := by
      exact hb.symm.trans (by
        change K.path.snd = aVertex H 0 at h
        exact h)
    have hi := H.vertex_injective hv
    simp [aVertex, bVertex] at hi
  exact {
    route := routeLengthOne H
    route_isPath := hroute_path
    route_length := by omega
    route_disjoint := routeLengthOne_disjoint H K hK
    first_steps_distinct := hfirst }

/--
@isnad1 id=ex.1h4v.s8.483c91d18ccd from=translated src=- shape=19edbc8a vocab=3b04f5d3
-/
theorem cycle8_of_connector_01_length_one
    (H : PentagramEarHull G) (K : Connector H 0 1)
    (hK : K.path.length = 1) :
    ∃ c : G.Walk (bVertex H 0) (bVertex H 0),
      c.IsCycle ∧ c.length = 8 := by
  exact cycle8_of_hull_return H 0 1 K
    (hullReturn_of_connector_01_length_one H K hK)

end PentagramEarHull

end Erdos64
