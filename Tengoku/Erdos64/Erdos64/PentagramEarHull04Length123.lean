import Tengoku.Erdos64.Erdos64.PentagramEarHull
import Tengoku.Erdos64.Erdos64.PentagramEarHullCasework

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

namespace PentagramEarHull

variable {V : Type u} {G : SimpleGraph V}

/-- The length-seven `(0,4)` hull route
`b0-a2-c2-c1-c0-c4-a4-b4`.-/
def route041 (H : PentagramEarHull G) :
    G.Walk (bVertex H 0) (bVertex H 4) :=
  SimpleGraph.Walk.cons (H.shifted_ab_adj 0).symm <|
    SimpleGraph.Walk.cons (H.ca_adj 2).symm <|
      SimpleGraph.Walk.cons (H.c_adj 1).symm <|
        SimpleGraph.Walk.cons (H.c_adj 0).symm <|
          SimpleGraph.Walk.cons (H.c_adj 4).symm <|
            SimpleGraph.Walk.cons (H.ca_adj 4) <|
              SimpleGraph.Walk.cons (H.ab_adj 4) .nil

/-- The length-six `(0,4)` hull route `b0-a2-c2-c3-c4-a4-b4`.-/
def route042 (H : PentagramEarHull G) :
    G.Walk (bVertex H 0) (bVertex H 4) :=
  SimpleGraph.Walk.cons (H.shifted_ab_adj 0).symm <|
    SimpleGraph.Walk.cons (H.ca_adj 2).symm <|
      SimpleGraph.Walk.cons (H.c_adj 2) <|
        SimpleGraph.Walk.cons (H.c_adj 3) <|
          SimpleGraph.Walk.cons (H.ca_adj 4) <|
            SimpleGraph.Walk.cons (H.ab_adj 4) .nil

/-- The length-five `(0,4)` hull route `b0-a0-c0-c4-a4-b4`.-/
def route043 (H : PentagramEarHull G) :
    G.Walk (bVertex H 0) (bVertex H 4) :=
  SimpleGraph.Walk.cons (H.ab_adj 0).symm <|
    SimpleGraph.Walk.cons (H.ca_adj 0).symm <|
      SimpleGraph.Walk.cons (H.c_adj 4).symm <|
        SimpleGraph.Walk.cons (H.ca_adj 4) <|
          SimpleGraph.Walk.cons (H.ab_adj 4) .nil

theorem route041_length (H : PentagramEarHull G) : H.route041.length = 7 := by
  rfl

theorem route042_length (H : PentagramEarHull G) : H.route042.length = 6 := by
  rfl

theorem route043_length (H : PentagramEarHull G) : H.route043.length = 5 := by
  rfl

private theorem route041_isPath (H : PentagramEarHull G) :
    H.route041.IsPath := by
  apply (SimpleGraph.Walk.isPath_def _).mpr
  change List.Nodup
    [H.vertex (.inr (.inr 0)), H.vertex (.inr (.inl 2)),
      H.vertex (.inl 2), H.vertex (.inl 1), H.vertex (.inl 0),
      H.vertex (.inl 4), H.vertex (.inr (.inl 4)),
      H.vertex (.inr (.inr 4))]
  let xs : List (Sum (Fin 5) (Sum (Fin 5) (Fin 5))) :=
    [.inr (.inr 0), .inr (.inl 2), .inl 2, .inl 1, .inl 0,
      .inl 4, .inr (.inl 4), .inr (.inr 4)]
  have hxs : xs.Nodup := by decide
  exact List.Nodup.map H.vertex_injective hxs

private theorem route042_isPath (H : PentagramEarHull G) :
    H.route042.IsPath := by
  apply (SimpleGraph.Walk.isPath_def _).mpr
  change List.Nodup
    [H.vertex (.inr (.inr 0)), H.vertex (.inr (.inl 2)),
      H.vertex (.inl 2), H.vertex (.inl 3), H.vertex (.inl 4),
      H.vertex (.inr (.inl 4)), H.vertex (.inr (.inr 4))]
  let xs : List (Sum (Fin 5) (Sum (Fin 5) (Fin 5))) :=
    [.inr (.inr 0), .inr (.inl 2), .inl 2, .inl 3, .inl 4,
      .inr (.inl 4), .inr (.inr 4)]
  have hxs : xs.Nodup := by decide
  exact List.Nodup.map H.vertex_injective hxs

private theorem route043_isPath (H : PentagramEarHull G) :
    H.route043.IsPath := by
  apply (SimpleGraph.Walk.isPath_def _).mpr
  change List.Nodup
    [H.vertex (.inr (.inr 0)), H.vertex (.inr (.inl 0)),
      H.vertex (.inl 0), H.vertex (.inl 4),
      H.vertex (.inr (.inl 4)), H.vertex (.inr (.inr 4))]
  let xs : List (Sum (Fin 5) (Sum (Fin 5) (Fin 5))) :=
    [.inr (.inr 0), .inr (.inl 0), .inl 0, .inl 4,
      .inr (.inl 4), .inr (.inr 4)]
  have hxs : xs.Nodup := by decide
  exact List.Nodup.map H.vertex_injective hxs

private theorem connector_tail_interior_04
    (K : Connector H 0 4) {v : V}
    (hv : v ∈ K.path.support.tail) (hv4 : v ≠ bVertex H 4) :
    v ∈ K.path.support.tail.dropLast := by
  apply List.mem_dropLast_of_mem_of_ne_getLast hv
  grind [K.path.getLast_support]

private theorem connector_snd_ne_endpoint_04
    (K : Connector H 0 4) (hK : K.path.length = 2 ∨ K.path.length = 3) :
    K.path.snd ≠ bVertex H 4 := by
  intro hb
  have hnil : ¬ K.path.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    rcases hK with hK | hK <;> omega
  have hnodup := K.isPath.support_nodup
  have h1 : 1 < K.path.support.length := by
    simp [K.path.length_support]
    rcases hK with hK | hK <;> omega
  have hlast : K.path.support[K.path.length]'(by
      simp [K.path.length_support]) = bVertex H 4 := by
    exact K.path.support_getElem_length
  have heq : K.path.support[1]'h1 =
      K.path.support[K.path.length]'(by
        simp [K.path.length_support]) := by
    rw [← K.path.snd_eq_support_getElem_one hnil]
    exact hb.trans hlast.symm
  have hidx := (List.Nodup.getElem_inj_iff hnodup).mp heq
  rcases hK with hK | hK <;> omega

private theorem route041_disjoint
    (H : PentagramEarHull G) (K : Connector H 0 4)
    (hK : K.path.length = 1) :
    (K.path.take K.path.length).support.tail.Disjoint
      (H.route041.take H.route041.length).reverse.support.tail := by
  rw [K.path.take_of_length_le (Nat.le_refl _),
    H.route041.take_of_length_le (Nat.le_refl _)]
  simp only [SimpleGraph.Walk.support_copy]
  apply List.disjoint_left.2
  intro v hvK hvR
  have hvR' : v ∈ H.route041.reverse.support := List.mem_of_mem_tail hvR
  have hvh : v ∈ hull H := by
    simp [route041, hull, cVertex, aVertex, bVertex] at hvR' ⊢
    aesop
  have hv4 : v ≠ bVertex H 4 := by
    intro hv4
    subst v
    simp [route041, cVertex, aVertex, bVertex] at hvR
    rcases hvR with h | h | h | h | h | h | h <;>
      have hi := H.vertex_injective h <;> simp_all
  exact K.interior_disjoint v (connector_tail_interior_04 K hvK hv4) hvh

private theorem route042_disjoint
    (H : PentagramEarHull G) (K : Connector H 0 4)
    (hK : K.path.length = 2) :
    (K.path.take K.path.length).support.tail.Disjoint
      (H.route042.take H.route042.length).reverse.support.tail := by
  rw [K.path.take_of_length_le (Nat.le_refl _),
    H.route042.take_of_length_le (Nat.le_refl _)]
  simp only [SimpleGraph.Walk.support_copy]
  apply List.disjoint_left.2
  intro v hvK hvR
  have hvR' : v ∈ H.route042.reverse.support := List.mem_of_mem_tail hvR
  have hvh : v ∈ hull H := by
    simp [route042, hull, cVertex, aVertex, bVertex] at hvR' ⊢
    aesop
  have hv4 : v ≠ bVertex H 4 := by
    intro hv4
    subst v
    simp [route042, cVertex, aVertex, bVertex] at hvR
    rcases hvR with h | h | h | h | h | h <;>
      have hi := H.vertex_injective h <;> simp_all
  exact K.interior_disjoint v (connector_tail_interior_04 K hvK hv4) hvh

private theorem route043_disjoint
    (H : PentagramEarHull G) (K : Connector H 0 4)
    (hK : K.path.length = 3) :
    (K.path.take K.path.length).support.tail.Disjoint
      (H.route043.take H.route043.length).reverse.support.tail := by
  rw [K.path.take_of_length_le (Nat.le_refl _),
    H.route043.take_of_length_le (Nat.le_refl _)]
  simp only [SimpleGraph.Walk.support_copy]
  apply List.disjoint_left.2
  intro v hvK hvR
  have hvR' : v ∈ H.route043.reverse.support := List.mem_of_mem_tail hvR
  have hvh : v ∈ hull H := by
    simp [route043, hull, cVertex, aVertex, bVertex] at hvR' ⊢
    aesop
  have hv4 : v ≠ bVertex H 4 := by
    intro hv4
    subst v
    simp [route043, cVertex, aVertex, bVertex] at hvR
    rcases hvR with h | h | h | h | h <;>
      have hi := H.vertex_injective h <;> simp_all
  exact K.interior_disjoint v (connector_tail_interior_04 K hvK hv4) hvh

def hullReturn_of_connector_04_length_one
    (H : PentagramEarHull G) (K : Connector H 0 4)
    (hK : K.path.length = 1) : HullReturn H 0 4 K := by
  have hfirst : K.path.snd ≠ H.route041.snd := by
    intro h
    have hnil : ¬ K.path.Nil := by
      rw [SimpleGraph.Walk.not_nil_iff_lt_length]
      omega
    have hsnd : K.path.snd = bVertex H 4 := by
      rw [K.path.snd_eq_support_getElem_one hnil]
      simpa [hK] using K.path.support_getElem_length
    have : bVertex H 4 = aVertex H 2 := by
      calc
        bVertex H 4 = K.path.snd := hsnd.symm
        _ = H.route041.snd := h
        _ = aVertex H 2 := by rfl
    have hi := H.vertex_injective this
    simp [aVertex, bVertex] at hi
  exact {
    route := H.route041
    route_isPath := by exact route041_isPath H
    route_length := by rw [route041_length]; omega
    route_disjoint := route041_disjoint H K hK
    first_steps_distinct := hfirst }

def hullReturn_of_connector_04_length_two
    (H : PentagramEarHull G) (K : Connector H 0 4)
    (hK : K.path.length = 2) : HullReturn H 0 4 K := by
  have hfirst : K.path.snd ≠ H.route042.snd := by
    intro h
    apply K.interior_disjoint _
      (connector_tail_interior_04 K
        (K.path.snd_mem_tail_support (by
          rw [SimpleGraph.Walk.not_nil_iff_lt_length]
          omega))
        (connector_snd_ne_endpoint_04 K (Or.inl hK)))
    rw [show H.route042.snd = aVertex H 2 by rfl] at h
    rw [h]
    exact Set.mem_union_left _ (Set.mem_union_right _ ⟨2, rfl⟩)
  exact {
    route := H.route042
    route_isPath := route042_isPath H
    route_length := by rw [route042_length]; omega
    route_disjoint := route042_disjoint H K hK
    first_steps_distinct := hfirst }

def hullReturn_of_connector_04_length_three
    (H : PentagramEarHull G) (K : Connector H 0 4)
    (hK : K.path.length = 3) : HullReturn H 0 4 K := by
  have hfirst : K.path.snd ≠ H.route043.snd := by
    intro h
    apply K.interior_disjoint _
      (connector_tail_interior_04 K
        (K.path.snd_mem_tail_support (by
          rw [SimpleGraph.Walk.not_nil_iff_lt_length]
          omega))
        (connector_snd_ne_endpoint_04 K (Or.inr hK)))
    rw [show H.route043.snd = aVertex H 0 by rfl] at h
    rw [h]
    exact Set.mem_union_left _ (Set.mem_union_right _ ⟨0, rfl⟩)
  exact {
    route := H.route043
    route_isPath := route043_isPath H
    route_length := by rw [route043_length]; omega
    route_disjoint := route043_disjoint H K hK
    first_steps_distinct := hfirst }

theorem cycle8_of_connector_04_length_one
    (H : PentagramEarHull G) (K : Connector H 0 4)
    (hK : K.path.length = 1) :
    ∃ c : G.Walk (bVertex H 0) (bVertex H 0),
      c.IsCycle ∧ c.length = 8 := by
  exact cycle8_of_hull_return H 0 4 K
    (hullReturn_of_connector_04_length_one H K hK)

theorem cycle8_of_connector_04_length_two
    (H : PentagramEarHull G) (K : Connector H 0 4)
    (hK : K.path.length = 2) :
    ∃ c : G.Walk (bVertex H 0) (bVertex H 0),
      c.IsCycle ∧ c.length = 8 := by
  exact cycle8_of_hull_return H 0 4 K
    (hullReturn_of_connector_04_length_two H K hK)

theorem cycle8_of_connector_04_length_three
    (H : PentagramEarHull G) (K : Connector H 0 4)
    (hK : K.path.length = 3) :
    ∃ c : G.Walk (bVertex H 0) (bVertex H 0),
      c.IsCycle ∧ c.length = 8 := by
  exact cycle8_of_hull_return H 0 4 K
    (hullReturn_of_connector_04_length_three H K hK)

end PentagramEarHull

end Erdos64
