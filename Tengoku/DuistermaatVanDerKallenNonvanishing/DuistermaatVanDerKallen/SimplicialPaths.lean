import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.PolygonalChain
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.SemialgebraicLine
import Tengoku.Seed.Analysis.Convex.SimplicialComplex.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Compactness, component finiteness, and uniform polygonal C¹ chains
for a fixed finite geometric simplicial complex. Constructing such a model
by semialgebraic triangulation and transporting these paths through Hardt
trivializations remain separate open obligations. -/

namespace DuistermaatVanDerKallen
noncomputable section
open Set

/-- A finite geometric simplicial complex has uniformly bounded polygonal
segment counts within each connected component. Each segment lies in one face.
@isnad1 id=ex.1h2v.s8.911cccb6a633 from=translated src=- shape=515f5bdf vocab=dfee1a3e
-/
theorem finite_simplicial_complex_uniform_segment_chains
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ x ∈ K.space, ∀ y ∈ connectedComponentIn K.space x,
      ∃ n ≤ N, ∃ node : ℕ → E, node 0 = x ∧ node n = y ∧
        ∀ k < n, ∃ s ∈ K.faces,
          segment ℝ (node k) (node (k + 1)) ⊆ convexHull ℝ (s : Set E) := by
  let : Finite K.faces := hK
  let C (s : K.faces) : Set E := convexHull ℝ (s.val : Set E)
  have hclosed (s : K.faces) : IsClosed (C s) := s.val.finite_toSet.isClosed_convexHull ℝ
  have hconvex (s : K.faces) : Convex ℝ (C s) := convex_convexHull ℝ _
  have hspace : (⋃ s : K.faces, C s) = K.space := by
    ext x
    simp [C, Geometry.SimplicialComplex.space]
  obtain ⟨N, hN, hchain⟩ := finite_closed_convex_cover_uniform_segment_chains C hclosed hconvex
  refine ⟨N, hN, fun x hx y hy => ?_⟩
  rw [hspace] at hchain
  obtain ⟨n, hn, node, h0, hend, hseg⟩ := hchain x hx y hy
  refine ⟨n, hn, node, h0, hend, fun k hk => ?_⟩
  obtain ⟨s, hs⟩ := hseg k hk
  exact ⟨s.val, s.property, hs⟩

/--
@isnad1 id=iscompac.1h2v.s6.3a13384f553f from=translated src=- shape=6494fa8f vocab=58f5f731
-/
theorem finite_simplicial_complex_isCompact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite) : IsCompact K.space := by
  rw [Geometry.SimplicialComplex.space]
  exact hK.isCompact_biUnion (fun s _ => s.finite_toSet.isCompact_convexHull ℝ)

/--
@isnad1 id=finite.1h2v.s6.71576c2a45f0 from=translated src=- shape=dd3dd261 vocab=38400088
-/
theorem finite_simplicial_complex_finite_components
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite) :
    Finite (ConnectedComponents K.space) := by
  let C : Set (Set E) := (fun s : Finset E => convexHull ℝ (s : Set E)) '' K.faces
  have hC : C.Finite := hK.image _
  apply finite_connectedComponents_of_finite_preconnected_cover hC
  · rintro A ⟨s, _, rfl⟩
    exact (convex_convexHull ℝ _).isPreconnected
  · ext x
    simp [C, Geometry.SimplicialComplex.space]

/-- The number of connected components is at most the number of faces.
@isnad1 id=le.1h2v.s7.c1d540a6da22 from=translated src=- shape=221da11a vocab=4e5369ef
-/
theorem finite_simplicial_complex_component_card_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite) :
    Nat.card (ConnectedComponents K.space) ≤ K.faces.ncard := by
  let C : Set (Set E) := (fun s : Finset E => convexHull ℝ (s : Set E)) '' K.faces
  have hC : C.Finite := hK.image _
  have hconn : ∀ A ∈ C, IsPreconnected A := by
    rintro A ⟨s, _, rfl⟩
    exact (convex_convexHull ℝ _).isPreconnected
  have hcover : ⋃₀ C = K.space := by
    ext x
    simp [C, Geometry.SimplicialComplex.space]
  exact (card_connectedComponents_le_of_finite_preconnected_cover hC hconn hcover).trans
    (Set.ncard_image_le hK)

/-- The full uniform C¹-chain conclusion on a fixed finite simplicial model.
Its compact radius bound is derived, not supplied as an assumption.
@isnad1 id=ex.1h2v.s7.e387259a717c from=translated src=- shape=6b662af5 vocab=b7b887ad
-/
theorem finite_simplicial_complex_uniform_C1_chains
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ L : ℝ, 1 ≤ L ∧
      ∀ x ∈ K.space, ∀ y ∈ connectedComponentIn K.space x,
        ∃ γ : C1ArcChain K.space x y, γ.pieces ≤ N ∧ γ.length ≤ L := by
  let : Finite K.faces := hK
  let C (s : K.faces) : Set E := convexHull ℝ (s.val : Set E)
  have hclosed (s : K.faces) : IsClosed (C s) := s.val.finite_toSet.isClosed_convexHull ℝ
  have hconvex (s : K.faces) : Convex ℝ (C s) := convex_convexHull ℝ _
  have hspace : (⋃ s : K.faces, C s) = K.space := by
    ext x
    simp [C, Geometry.SimplicialComplex.space]
  obtain ⟨B, hB⟩ := (finite_simplicial_complex_isCompact K hK).isBounded.exists_norm_le
  have hbound (s : K.faces) (z) (hz : z ∈ C s) : ‖z‖ ≤ max 0 B :=
    (hB z (Geometry.SimplicialComplex.convexHull_subset_space s.property hz)).trans (le_max_right _ _)
  have h := finite_closed_convex_cover_uniform_C1_chains C hclosed hconvex
    (max 0 B) (le_max_left _ _) hbound
  rw [hspace] at h
  exact h

end
end DuistermaatVanDerKallen
