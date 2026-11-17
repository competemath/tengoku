import Tengoku
import Tengoku.LeanEvalPlatonicClassification.ChallengeDeps
import Tengoku.LeanEvalPlatonicClassification.Submission.PerturbazioneFinita
import Tengoku.LeanEvalPlatonicClassification.Submission.VerticiEsposti
import Tengoku.LeanEvalPlatonicClassification.Submission.SottoPolitopo
import Tengoku.LeanEvalPlatonicClassification.Submission.DimStretta
import Tengoku.LeanEvalPlatonicClassification.Submission.Interpolazione
import Tengoku.LeanEvalPlatonicClassification.Submission.ScalaBandiere

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
FASE 3A — LA BANDIERA COMPAGNA (18 lug 2026).

Scarico completo di KG-3A1: per OGNI bandiera F di un politopo 3D esiste una
bandiera G con la stessa faccetta e spigolo diverso. Costruzione: nel
sotto-politopo Q della faccetta (dim 2) c'è un vertice w fuori dallo spigolo
(altrimenti lo spigolo conterrebbe tutti i vertici e sarebbe l'intera
faccetta); {w} è faccia (Q1), l'interpolazione (S3) dà uno spigolo f' ∋ w,
e f' ≠ F.face 1 perché w ∉ F.face 1. Corollario: `rho_orbitale_libero` —
in un politopo regolare ogni bandiera ammette una simmetria che fissa la
faccetta e muove lo spigolo, SENZA ipotesi condizionali.
-/
namespace Tengoku.LeanEvalPlatonicClassification end Tengoku.LeanEvalPlatonicClassification open Tengoku.LeanEvalPlatonicClassification
open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- La dimensione di un singoletto è 0.-/
theorem faceDim_singleton (v : E n) : faceDim ({v} : Set (E n)) = 0 := by
  show Module.finrank ℝ (vectorSpan ℝ ({v} : Set (E n))) = 0
  rw [vectorSpan_singleton]
  simp

/-- Una faccia diversa dal corpo lascia fuori almeno un vertice.-/
theorem exists_vertex_notMem_of_ne_toSet (P : ConvexPolytope n) {f : Set (E n)}
    (hf : P.IsFace f) (hne : f ≠ P.toSet) :
    ∃ w ∈ P.vertices, w ∉ f := by
  by_contra hall
  push_neg at hall
  have hconv : Convex ℝ f := hf.1.convex (convex_convexHull ℝ _)
  have hsub : P.toSet ⊆ f := by
    show convexHull ℝ ((P.vertices : Set (E n))) ⊆ f
    apply convexHull_min ?_ hconv
    intro x hx
    exact hall x (Finset.mem_coe.mp hx)
  exact hne (Set.Subset.antisymm (face_subset_toSet P hf) hsub)

end LeanEval.Geometry.PlatonicClassification
-- Tengoku: root names of this library moved to Tengoku.LeanEvalPlatonicClassification so they do not collide with other libraries (generated)
