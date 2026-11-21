import Tengoku.Erdos64.Erdos64.PentagramEarHullNormalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64.PentagramEarHull

universe u

variable {V : Type u} {G : SimpleGraph V}

private def reflect5Shifted (k i : Fin 5) : Fin 5 := reflect5 k i + 3

private theorem reflect5_succ_add_one (k i : Fin 5) :
    reflect5 k (i + 1) + 1 = reflect5 k i := by
  fin_cases k <;> fin_cases i <;> decide

private theorem reflect5_add_two (k i : Fin 5) :
    reflect5 k (i + 2) = reflect5 k i + 3 := by
  fin_cases k <;> fin_cases i <;> decide

private theorem reflect5_add_three_add_two (k i : Fin 5) :
    reflect5 k i + 3 + 2 = reflect5 k i := by
  fin_cases k <;> fin_cases i <;> decide

private theorem reflect5Shifted_bijective (k : Fin 5) :
    Function.Bijective (reflect5Shifted k) := by
  fin_cases k <;> decide

private def reflectVertexIndex (k : Fin 5) :
    Sum (Fin 5) (Sum (Fin 5) (Fin 5)) ->
      Sum (Fin 5) (Sum (Fin 5) (Fin 5))
  | .inl i => .inl (reflect5 k i)
  | .inr (.inl i) => .inr (.inl (reflect5 k i))
  | .inr (.inr i) => .inr (.inr (reflect5Shifted k i))

private theorem reflectVertexIndex_injective (k : Fin 5) :
    Function.Injective (reflectVertexIndex k) := by
  intro x y h
  rcases x with i | (i | i) <;> rcases y with j | (j | j) <;>
    simp_all [reflectVertexIndex, reflect5Shifted,
      (reflect5_bijective k).1.eq_iff,
      (reflect5Shifted_bijective k).1.eq_iff]

/-- The layer-aware reflection of a pentagram hull.  The `b` layer receives
the extra three-step offset needed to reverse the shifted `a/b` incidence.-/
def reflectHull (H : PentagramEarHull G) (k : Fin 5) : PentagramEarHull G where
  vertex := fun x => H.vertex (reflectVertexIndex k x)
  vertex_injective := H.vertex_injective.comp (reflectVertexIndex_injective k)
  c_adj i := by
    simpa only [reflectVertexIndex, reflect5_succ_add_one] using
      (H.c_adj (reflect5 k (i + 1))).symm
  ca_adj i := H.ca_adj (reflect5 k i)
  ab_adj i := by
    simpa only [reflectVertexIndex, reflect5Shifted,
      reflect5_add_three_add_two] using
      H.shifted_ab_adj (reflect5 k i + 3)
  shifted_ab_adj i := by
    simpa only [reflectVertexIndex, reflect5Shifted, reflect5_add_two] using
      H.ab_adj (reflect5 k i + 3)

/--
@isnad1 id=eq.0h5v.s5.843392b352f4 from=translated src=- shape=ff71d7b9 vocab=0a377b1f
-/
@[simp] theorem reflectHull_cVertex (H : PentagramEarHull G) (k i : Fin 5) :
    cVertex (reflectHull H k) i = cVertex H (reflect5 k i) := rfl

/--
@isnad1 id=eq.0h5v.s5.0dcd37b096cc from=translated src=- shape=ff71d7b9 vocab=cad60dc6
-/
@[simp] theorem reflectHull_aVertex (H : PentagramEarHull G) (k i : Fin 5) :
    aVertex (reflectHull H k) i = aVertex H (reflect5 k i) := rfl

/--
@isnad1 id=eq.0h5v.s5.467b96687d6b from=translated src=- shape=ff71d7b9 vocab=0900c23e
-/
@[simp] theorem reflectHull_bVertex (H : PentagramEarHull G) (k i : Fin 5) :
    bVertex (reflectHull H k) i = bVertex H (reflect5Shifted k i) := rfl

private theorem range_comp_bijective {W : Type u} (f : Fin 5 → W)
    (e : Fin 5 → Fin 5) (he : Function.Bijective e) :
    Set.range (fun i => f (e i)) = Set.range f := by
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨e i, rfl⟩
  · rintro ⟨i, hi⟩
    obtain ⟨j, hj⟩ := he.2 i
    exact ⟨j, by simpa only [hj] using hi⟩

/--
@isnad1 id=eq.0h4v.s4.9dd122aee292 from=translated src=- shape=05ecf525 vocab=43455861
-/
theorem hull_reflectHull (H : PentagramEarHull G) (k : Fin 5) :
    hull (reflectHull H k) = hull H := by
  change
    (Set.range (fun i => H.cVertex (reflect5 k i)) ∪
      Set.range (fun i => H.aVertex (reflect5 k i))) ∪
      Set.range (fun i => H.bVertex (reflect5Shifted k i)) =
    (Set.range H.cVertex ∪ Set.range H.aVertex) ∪ Set.range H.bVertex
  rw [range_comp_bijective H.cVertex (reflect5 k) (reflect5_bijective k),
    range_comp_bijective H.aVertex (reflect5 k) (reflect5_bijective k),
    range_comp_bijective H.bVertex (reflect5Shifted k)
      (reflect5Shifted_bijective k)]

/-- Transport a connector whose old endpoints are the reflected image of the
new endpoint labels.  This transports existing data only and creates no new
connector-existence claim.-/
def Connector.ofReflectIndices (H : PentagramEarHull G) (k i j : Fin 5)
    (K : Connector H (reflect5Shifted k i) (reflect5Shifted k j)) :
    Connector (reflectHull H k) i j where
  distinct := fun h => K.distinct (congrArg (reflect5Shifted k) h)
  path := K.path
  isPath := K.isPath
  length_one_to_three := K.length_one_to_three
  interior_disjoint := by
    intro v hv hh
    exact K.interior_disjoint v hv (by rwa [hull_reflectHull] at hh)

/--
@isnad1 id=eq.0h7v.s6.8691ae5969c5 from=translated src=- shape=e106d802 vocab=688050fe
-/
@[simp] theorem Connector.ofReflectIndices_path
    (H : PentagramEarHull G) (k i j : Fin 5)
    (K : Connector H (reflect5Shifted k i) (reflect5Shifted k j)) :
    (Connector.ofReflectIndices H k i j K).path = K.path := rfl

/-- Transport a normalized `HullReturn` back through the layer-aware
reflection, preserving the original connector and route data.-/
def HullReturn.ofReflectIndices (H : PentagramEarHull G) (k i j : Fin 5)
    (K : Connector H (reflect5Shifted k i) (reflect5Shifted k j))
    (R : HullReturn (reflectHull H k) i j
      (Connector.ofReflectIndices H k i j K)) :
    HullReturn H (reflect5Shifted k i) (reflect5Shifted k j) K where
  route := R.route
  route_isPath := R.route_isPath
  route_length := R.route_length
  route_disjoint := R.route_disjoint
  first_steps_distinct := R.first_steps_distinct

end Erdos64.PentagramEarHull
