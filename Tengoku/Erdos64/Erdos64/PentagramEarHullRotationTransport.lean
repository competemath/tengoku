import Tengoku.Erdos64.Erdos64.PentagramEarHullNormalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64.PentagramEarHull

universe u
variable {V : Type u} {G : SimpleGraph V}

private def rotateVertexIndex (k : Fin 5) :
    Sum (Fin 5) (Sum (Fin 5) (Fin 5)) ->
      Sum (Fin 5) (Sum (Fin 5) (Fin 5))
  | .inl i => .inl (rotate5 k i)
  | .inr (.inl i) => .inr (.inl (rotate5 k i))
  | .inr (.inr i) => .inr (.inr (rotate5 k i))

private theorem rotateVertexIndex_injective (k : Fin 5) :
    Function.Injective (rotateVertexIndex k) := by
  intro x y h
  rcases x with i | (i | i) <;> rcases y with j | (j | j) <;>
    simp_all [rotateVertexIndex, (rotate5_bijective k).1.eq_iff]

private theorem rotate5_add_two (k i : Fin 5) :
    rotate5 k (i + 2) = rotate5 k i + 2 := by
  fin_cases k <;> fin_cases i <;> decide

private theorem rotate5_zero (k : Fin 5) : rotate5 k 0 = k := by
  fin_cases k <;> decide

/-- New index `t` denotes the old index `rotate5 k t`.-/
def rotateHull (H : PentagramEarHull G) (k : Fin 5) : PentagramEarHull G where
  vertex := fun x => H.vertex (rotateVertexIndex k x)
  vertex_injective := H.vertex_injective.comp (rotateVertexIndex_injective k)
  c_adj i := by
    simpa only [rotateVertexIndex, rotate5_succ] using H.c_adj (rotate5 k i)
  ca_adj i := H.ca_adj (rotate5 k i)
  ab_adj i := H.ab_adj (rotate5 k i)
  shifted_ab_adj i := by
    simpa only [rotateVertexIndex, rotate5_add_two] using H.shifted_ab_adj (rotate5 k i)

@[simp] theorem rotateHull_cVertex (H : PentagramEarHull G) (k i : Fin 5) :
    cVertex (rotateHull H k) i = cVertex H (rotate5 k i) := rfl

@[simp] theorem rotateHull_aVertex (H : PentagramEarHull G) (k i : Fin 5) :
    aVertex (rotateHull H k) i = aVertex H (rotate5 k i) := rfl

@[simp] theorem rotateHull_bVertex (H : PentagramEarHull G) (k i : Fin 5) :
    bVertex (rotateHull H k) i = bVertex H (rotate5 k i) := rfl

private theorem range_comp_rotate5 {W : Type u} (f : Fin 5 -> W) (k : Fin 5) :
    Set.range (fun i => f (rotate5 k i)) = Set.range f := by
  ext v
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨rotate5 k i, hi⟩
  · rintro ⟨i, hi⟩
    obtain ⟨j, hj⟩ := (rotate5_bijective k).2 i
    exact ⟨j, by simpa only [hj] using hi⟩

theorem hull_rotateHull (H : PentagramEarHull G) (k : Fin 5) :
    hull (rotateHull H k) = hull H := by
  change
    (Set.range (fun i => H.cVertex (rotate5 k i)) ∪
      Set.range (fun i => H.aVertex (rotate5 k i))) ∪
      Set.range (fun i => H.bVertex (rotate5 k i)) =
    (Set.range H.cVertex ∪ Set.range H.aVertex) ∪ Set.range H.bVertex
  rw [range_comp_rotate5, range_comp_rotate5, range_comp_rotate5]

/-- Reindexing changes endpoint labels, not the ambient walk.-/
def Connector.rotateIndices (H : PentagramEarHull G) (k i j : Fin 5)
    (K : Connector H (rotate5 k i) (rotate5 k j)) :
    Connector (rotateHull H k) i j where
  distinct := fun h => K.distinct (congrArg (rotate5 k) h)
  path := K.path
  isPath := K.isPath
  length_one_to_three := K.length_one_to_three
  interior_disjoint := by
    intro v hv hh
    exact K.interior_disjoint v hv (by rwa [hull_rotateHull] at hh)

@[simp] theorem Connector.rotateIndices_path
    (H : PentagramEarHull G) (k i j : Fin 5)
    (K : Connector H (rotate5 k i) (rotate5 k j)) :
    (Connector.rotateIndices H k i j K).path = K.path := rfl

/-- Return routes transport back along the same definitional endpoints.-/
def HullReturn.ofRotateIndices (H : PentagramEarHull G) (k i j : Fin 5)
    (K : Connector H (rotate5 k i) (rotate5 k j))
    (R : HullReturn (rotateHull H k) i j (Connector.rotateIndices H k i j K)) :
    HullReturn H (rotate5 k i) (rotate5 k j) K where
  route := R.route
  route_isPath := R.route_isPath
  route_length := R.route_length
  route_disjoint := R.route_disjoint
  first_steps_distinct := R.first_steps_distinct

/-- Every connector admits rotation-only normalization to `0,d`, `d != 0`.-/
theorem exists_rotated_connector (H : PentagramEarHull G) {i j : Fin 5}
    (K : Connector H i j) :
    ∃ d : Fin 5, d ≠ 0 ∧ Nonempty (Connector (rotateHull H i) 0 d) := by
  obtain ⟨d, hd⟩ := (rotate5_bijective i).2 j
  have hz : rotate5 i 0 = i := rotate5_zero i
  have hne : d ≠ 0 := by
    intro h
    exact K.distinct (by simpa only [h, hz] using hd)
  have K' : Connector H (rotate5 i 0) (rotate5 i d) := by
    simpa only [hz, hd] using K
  exact ⟨d, hne, ⟨Connector.rotateIndices H i 0 d K'⟩⟩

end Erdos64.PentagramEarHull
