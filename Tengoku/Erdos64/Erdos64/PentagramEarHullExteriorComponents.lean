import Tengoku.Erdos64.Erdos64.PentagramEarHull

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

namespace PentagramEarHull

variable {V : Type u} {G : SimpleGraph V}

/-- The induced graph on the complement of all fifteen hull vertices.-/
def exteriorGraph (H : PentagramEarHull G) :
    SimpleGraph {v : V // v ∉ H.hull} :=
  G.induce H.hullᶜ

/-- All actual connected components of the hull complement.-/
noncomputable def exteriorComponents (H : PentagramEarHull G) [Fintype V] :
    Finset H.exteriorGraph.ConnectedComponent := by
  classical
  letI : Fintype H.exteriorGraph.ConnectedComponent := Fintype.ofFinite _
  exact Finset.univ

@[simp] theorem mem_exteriorComponents (H : PentagramEarHull G) [Fintype V]
    (C : H.exteriorGraph.ConnectedComponent) : C ∈ H.exteriorComponents := by
  classical
  simp [exteriorComponents]

/-- The ambient finite carrier of an actual hull-complement component.-/
noncomputable def exteriorComponentCarrier (H : PentagramEarHull G) [Fintype V]
    (C : H.exteriorGraph.ConnectedComponent) : Finset V := by
  classical
  exact C.supp.toFinset.image Subtype.val

@[simp] theorem mem_exteriorComponentCarrier_iff (H : PentagramEarHull G)
    [Fintype V] (C : H.exteriorGraph.ConnectedComponent) (v : V) :
    v ∈ H.exteriorComponentCarrier C ↔
      ∃ hv : v ∉ H.hull, (⟨v, hv⟩ : {w : V // w ∉ H.hull}) ∈ C.supp := by
  classical
  simp only [exteriorComponentCarrier, Finset.mem_image, Set.mem_toFinset]
  constructor
  · rintro ⟨⟨w, hw⟩, hC, rfl⟩
    exact ⟨hw, hC⟩
  · rintro ⟨hv, hC⟩
    exact ⟨⟨v, hv⟩, hC, rfl⟩

/-- Components are nonempty by the quotient connected-component definition.-/
theorem exteriorComponentCarrier_nonempty (H : PentagramEarHull G) [Fintype V]
    (C : H.exteriorGraph.ConnectedComponent) :
    (H.exteriorComponentCarrier C).Nonempty := by
  obtain ⟨⟨v, hv⟩, hC⟩ := C.nonempty_supp
  exact ⟨v, (H.mem_exteriorComponentCarrier_iff C v).2 ⟨hv, hC⟩⟩

theorem exteriorComponentCarrier_not_mem_hull (H : PentagramEarHull G)
    [Fintype V] (C : H.exteriorGraph.ConnectedComponent) {v : V}
    (hv : v ∈ H.exteriorComponentCarrier C) : v ∉ H.hull := by
  obtain ⟨hext, _⟩ := (H.mem_exteriorComponentCarrier_iff C v).1 hv
  exact hext

/-- Distinct actual components have disjoint ambient carriers.-/
theorem exteriorComponentCarrier_pairwise_disjoint (H : PentagramEarHull G)
    [Fintype V] :
    Pairwise (fun C D : H.exteriorGraph.ConnectedComponent =>
      Disjoint (H.exteriorComponentCarrier C) (H.exteriorComponentCarrier D)) := by
  classical
  intro C D hne
  apply Finset.disjoint_left.2
  intro v hvC hvD
  obtain ⟨hv, hC⟩ := (H.mem_exteriorComponentCarrier_iff C v).1 hvC
  obtain ⟨hv', hD⟩ := (H.mem_exteriorComponentCarrier_iff D v).1 hvD
  exact hne (SimpleGraph.ConnectedComponent.eq_of_common_vertex hC hD)

/-- An ambient edge leaving a component must enter the hull.-/
theorem exteriorComponentCarrier_adj_closure (H : PentagramEarHull G)
    [Fintype V] (C : H.exteriorGraph.ConnectedComponent) {x y : V}
    (hx : x ∈ H.exteriorComponentCarrier C) (hxy : G.Adj x y) :
    y ∈ H.exteriorComponentCarrier C ∨ y ∈ H.hull := by
  classical
  by_cases hy : y ∈ H.hull
  · exact Or.inr hy
  · apply Or.inl
    obtain ⟨hxext, hxC⟩ := (H.mem_exteriorComponentCarrier_iff C x).1 hx
    have hxyext : H.exteriorGraph.Adj ⟨x, hxext⟩ ⟨y, hy⟩ := hxy
    exact (H.mem_exteriorComponentCarrier_iff C y).2
      ⟨hy, (C.mem_supp_congr_adj hxyext).1 hxC⟩

/-- Every exterior vertex belongs to an actual indexed component carrier.-/
theorem exists_exteriorComponentCarrier_of_not_mem_hull (H : PentagramEarHull G)
    [Fintype V] {v : V} (hv : v ∉ H.hull) :
    ∃ C ∈ H.exteriorComponents, v ∈ H.exteriorComponentCarrier C := by
  let C := H.exteriorGraph.connectedComponentMk ⟨v, hv⟩
  refine ⟨C, H.mem_exteriorComponents C, ?_⟩
  apply (H.mem_exteriorComponentCarrier_iff C v).2
  exact ⟨hv, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩

end PentagramEarHull

end Erdos64
