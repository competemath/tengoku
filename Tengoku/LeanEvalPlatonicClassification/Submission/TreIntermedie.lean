import Tengoku
import Tengoku.LeanEvalPlatonicClassification.Submission.BandieraVertice
import Tengoku.LeanEvalPlatonicClassification.Submission.SecondoIntermedio

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.LeanEvalPlatonicClassification end Tengoku.LeanEvalPlatonicClassification open Tengoku.LeanEvalPlatonicClassification
open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/--
@isnad1 id=ex.1h2v.s6.07f683c24b40 from=translated src=- shape=470f1385 vocab=cfa63a3f
-/
theorem tre_vertici_di_poligono (P : ConvexPolytope n)
    (hdim : faceDim P.toSet = 2) :
    ∃ u v w : Set (E n),
      (P.IsFace u ∧ faceDim u = 0) ∧ (P.IsFace v ∧ faceDim v = 0) ∧
      (P.IsFace w ∧ faceDim w = 0) ∧ u ≠ v ∧ u ≠ w ∧ v ≠ w := by
  classical
  have hdim_vertices :
      Module.finrank ℝ (vectorSpan ℝ (P.vertices : Set (E n))) = 2 := by
    have hspan : vectorSpan ℝ P.toSet =
        vectorSpan ℝ (P.vertices : Set (E n)) := by
      rw [← direction_affineSpan, ← direction_affineSpan]
      exact congrArg AffineSubspace.direction
        (affineSpan_convexHull (P.vertices : Set (E n)))
    rw [← hspan]
    exact hdim
  let vertexPoint : {x // x ∈ (P.vertices : Set (E n))} → E n :=
    fun x => x.1
  letI : Nonempty {x // x ∈ (P.vertices : Set (E n))} := by
    obtain ⟨x, hx⟩ := P.vertices_nonempty
    exact ⟨⟨x, by exact_mod_cast hx⟩⟩
  have hrange : Set.range vertexPoint = (P.vertices : Set (E n)) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hcard_bound := finrank_vectorSpan_range_add_one_le ℝ vertexPoint
  rw [hrange, hdim_vertices] at hcard_bound
  have hcard_eq : Fintype.card {x // x ∈ (P.vertices : Set (E n))} =
      P.vertices.card := by
    simp
  have hthree : 2 < P.vertices.card := by
    rw [hcard_eq] at hcard_bound
    omega
  obtain ⟨u, hu, v, hv, w, hw, huv, huw, hvw⟩ :=
    Finset.two_lt_card.mp hthree
  refine ⟨{u}, {v}, {w},
    ⟨vertex_isFace P hu, faceDim_singleton u⟩,
    ⟨vertex_isFace P hv, faceDim_singleton v⟩,
    ⟨vertex_isFace P hw, faceDim_singleton w⟩, ?_, ?_, ?_⟩
  · simpa using huv
  · simpa using huw
  · simpa using hvw

end LeanEval.Geometry.PlatonicClassification
-- Tengoku: root names of this library moved to Tengoku.LeanEvalPlatonicClassification so they do not collide with other libraries (generated)
