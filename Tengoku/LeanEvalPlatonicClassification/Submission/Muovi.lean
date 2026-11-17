import Tengoku
import Tengoku.LeanEvalPlatonicClassification.ChallengeDeps
import Tengoku.LeanEvalPlatonicClassification.Submission.InvarianteSimilarita
import Tengoku.LeanEvalPlatonicClassification.Submission.SimilarEquiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
RIGIDITÀ — IL POLITOPO TRASPORTATO DA UN'ISOMETRIA (19 lug 2026).

Gemello isometrico di `scala`: per usare la registrazione (l'isometria
`g` che allinea vertice e raggi) occorre poter applicare `g` a un
politopo e ottenere di nuovo un politopo del contratto. Come per
l'omotetia, il punto è che un'isometria affine è un'equivalenza affine,
quindi trasporta punti estremi in punti estremi e hull in hull.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Il politopo immagine sotto un'isometria affine.-/
noncomputable def muovi (g : Isom n) (P : ConvexPolytope n) :
    ConvexPolytope n where
  vertices := P.vertices.image (g : E n → E n)
  vertices_nonempty := by
    obtain ⟨v, hv⟩ := P.vertices_nonempty
    exact ⟨g v, Finset.mem_image_of_mem _ hv⟩
  vertices_eq_extremePoints := by
    classical
    have hset : ((P.vertices.image (g : E n → E n) : Finset (E n)) :
        Set (E n)) = (⇑g.toAffineEquiv) '' ((P.vertices : Set (E n))) := by
      ext x
      simp
    rw [hset]
    have hhull : convexHull ℝ ((⇑g.toAffineEquiv) ''
        ((P.vertices : Set (E n)))) =
        (⇑g.toAffineEquiv) '' (convexHull ℝ ((P.vertices : Set (E n)))) := by
      have h1 := g.toAffineEquiv.toAffineMap.image_convexHull
        ((P.vertices : Set (E n)))
      have hco : (⇑g.toAffineEquiv.toAffineMap : E n → E n) =
          ⇑g.toAffineEquiv := rfl
      rw [hco] at h1
      exact h1.symm
    rw [hhull, extremePoints_image_affineEquiv]
    congr 1
    exact P.vertices_eq_extremePoints

/--
@isnad1 id=eq.0h3v.s8.6d103fc4b360 from=translated src=- shape=638f0944 vocab=33bd391d
-/
theorem muovi_toSet (g : Isom n) (P : ConvexPolytope n) :
    (muovi g P).toSet = (g : E n → E n) '' P.toSet := by
  classical
  show convexHull ℝ (((P.vertices.image (g : E n → E n) : Finset (E n))) :
    Set (E n)) = _
  have hset : ((P.vertices.image (g : E n → E n) : Finset (E n)) :
      Set (E n)) = (⇑g.toAffineEquiv) '' ((P.vertices : Set (E n))) := by
    ext x
    simp
  rw [hset]
  have h1 := g.toAffineEquiv.toAffineMap.image_convexHull
    ((P.vertices : Set (E n)))
  have hco : (⇑g.toAffineEquiv.toAffineMap : E n → E n) =
      ⇑g.toAffineEquiv := rfl
  rw [hco] at h1
  rw [← h1]
  rfl

/-- **MUOVERE NON CAMBIA LA CLASSE DI SIMILARITÀ**.
@isnad1 id=similar.0h3v.s3.93fa61ea0b1c from=translated src=- shape=e2696eeb vocab=42dfe747
-/
theorem similar_muovi (g : Isom n) (P : ConvexPolytope n) :
    Similar P (muovi g P) := by
  refine ⟨1, one_pos, g, ?_⟩
  rw [muovi_toSet]
  simp

/-- I vertici del politopo mosso sono le immagini dei vertici.
@isnad1 id=mem.1h4v.s8.59ac135a77ab from=translated src=- shape=ffb72334 vocab=3aa36782
-/
theorem mem_vertices_muovi (g : Isom n) (P : ConvexPolytope n) {v : E n}
    (hv : v ∈ P.vertices) : g v ∈ (muovi g P).vertices :=
  Finset.mem_image_of_mem _ hv

end LeanEval.Geometry.PlatonicClassification
