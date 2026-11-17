import Tengoku
import Tengoku.LeanEvalPlatonicClassification.Submission.FettaVertice
import Tengoku.LeanEvalPlatonicClassification.Submission.SottoPolitopo
import Tengoku.LeanEvalPlatonicClassification.Submission.VerticiEsposti
import Tengoku.LeanEvalPlatonicClassification.Submission.VertexFigureRidge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
LA FIGURA AL VERTICE ESISTE — CHIUSURA DEL SOTTO-KILL-GATE (21 lug 2026).

`vertexFigure_galois_exists` fornisce, per ogni faccia `B` e vertice `v`,
i dati di Galois `VertexFigureGaloisData`: la figura è il politopo-fetta
di `FettaVertice` al livello separatore, l'equivalenza è
`F ↦ F ∩ {l = c}` con inversa data da `faccia_dalla_fetta`, l'ordine è
preservato da `fetta_mono` e lo shift dimensionale è `fetta_faceDim`.

Corollari apicali, ora INCONDIZIONATI:
* `vertexStar_ridge_connected` — il sotto-kill-gate della campagna;
* `ridgeConnectedAboveOne_sempre` — il muro del ridge-graph, per ogni
  politopo e ogni dimensione;
* `galleryConnected_sempre` — la connettività globale delle gallerie;
* `vertices_eq_simpleVertexOrbit_sempre` — U4: i vertici sono l'orbita
  del vertice base sotto il gruppo delle riflessioni semplici.
-/
namespace Tengoku.LeanEvalPlatonicClassification end Tengoku.LeanEvalPlatonicClassification open Tengoku.LeanEvalPlatonicClassification
open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Il livello separatore esiste per ogni vertice di un politopo di
dimensione positiva.-/
theorem esiste_datiFetta (Q : ConvexPolytope n) {v : E n}
    (hv : v ∈ Q.vertices) (hdQ : 1 ≤ faceDim Q.toSet) :
    Nonempty (DatiFetta Q v) := by
  classical
  obtain ⟨l, hl⟩ := (vertex_isFace Q hv).1 (Set.singleton_nonempty v)
  have hvmem : v ∈ ({v} : Set (E n)) := Set.mem_singleton v
  rw [hl] at hvmem
  have hstrict : ∀ u ∈ Q.vertices, u ≠ v → l u < l v := by
    intro u huV huv
    have huT : u ∈ Q.toSet := subset_convexHull ℝ _ (by exact_mod_cast huV)
    rcases lt_or_eq_of_le (hvmem.2 u huT) with h | h
    · exact h
    · exfalso
      apply huv
      have hu1 : u ∈ ({v} : Set (E n)) := by
        rw [hl]
        exact ⟨huT, fun z hz => le_trans (hvmem.2 z hz) (le_of_eq h.symm)⟩
      exact Set.mem_singleton_iff.mp hu1
  have hW : (Q.vertices.erase v).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hverts : Q.vertices = {v} := by
      apply Finset.eq_of_subset_of_card_le
      · intro w hw
        by_contra hwv
        have hmem : w ∈ Q.vertices.erase v :=
          Finset.mem_erase.mpr ⟨by simpa using hwv, hw⟩
        rw [hempty] at hmem
        exact absurd hmem (Finset.notMem_empty w)
      · have h1 : 1 ≤ Q.vertices.card := Finset.card_pos.mpr ⟨v, hv⟩
        simpa using h1
    have hT : Q.toSet = ({v} : Set (E n)) := by
      show convexHull ℝ ((Q.vertices : Finset (E n)) : Set (E n)) = _
      rw [hverts]
      simp
    rw [hT, faceDim_singleton] at hdQ
    omega
  obtain ⟨m, hmW, hmmax⟩ := (Q.vertices.erase v).exists_max_image l hW
  have hmlt : l m < l v :=
    hstrict m (Finset.mem_of_mem_erase hmW) (Finset.ne_of_mem_erase hmW)
  refine ⟨⟨l, (l v + l m) / 2, hv, by linarith, ?_, hW⟩⟩
  intro w hwV hwv
  have hle := hmmax w (Finset.mem_erase.mpr ⟨hwv, hwV⟩)
  linarith

/-- **LA FIGURA AL VERTICE ESISTE.**  Il sotto-kill-gate della campagna
è chiuso: ogni intervallo di facce sopra un vertice ammette una vera
figura al vertice con la corrispondenza di Galois e lo shift
dimensionale.-/
theorem vertexFigure_galois_exists : VertexFigureGaloisExists := by
  intro n P B hB v hv hdB
  classical
  have hQT : (facePolytope P hB).toSet = B := facePolytope_toSet P hB
  have hdQ : 1 ≤ faceDim (facePolytope P hB).toSet := by
    rw [hQT]
    exact hdB
  obtain ⟨D⟩ := esiste_datiFetta (facePolytope P hB) hv hdQ
  choose Finv hFinvQ hFinvV hFinvD hFinvS using
    fun (G : PolytopeFace D.politopo) => D.faccia_dalla_fetta G.isFace
  refine ⟨⟨D.politopo,
    { toFun := fun F =>
        ⟨F.carrier ∩ {x | D.l x = D.c},
          D.faccia_fetta
            (facePolytope_isFace_of P hB F.isFace F.subset_base)
            F.mem_vertex F.dim_pos⟩
      invFun := fun G =>
        ⟨Finv G, isFace_of_facePolytope P hB (hFinvQ G),
          by
            have hsub := face_subset_toSet (facePolytope P hB) (hFinvQ G)
            rwa [hQT] at hsub,
          hFinvV G, hFinvD G⟩
      left_inv := ?_
      right_inv := ?_ }, ?_, ?_⟩⟩
  · -- left_inv: l'unicità della faccia con fetta data
    intro F
    apply PositiveVertexStarFace.ext
    have hQF : (facePolytope P hB).IsFace F.carrier :=
      facePolytope_isFace_of P hB F.isFace F.subset_base
    have hs := hFinvS ⟨F.carrier ∩ {x | D.l x = D.c},
      D.faccia_fetta (facePolytope_isFace_of P hB F.isFace F.subset_base)
        F.mem_vertex F.dim_pos⟩
    apply Set.Subset.antisymm
    · exact D.fetta_mono (hFinvQ _) (hFinvV _) hQF F.mem_vertex hs.subset
    · exact D.fetta_mono hQF F.mem_vertex (hFinvQ _) (hFinvV _)
        hs.symm.subset
  · -- right_inv: la fetta della faccia scelta è la faccia di partenza
    intro G
    apply PolytopeFace.ext
    exact hFinvS G
  · -- map_subset_iff
    intro F G
    constructor
    · intro hsub
      exact fun x hx => ⟨hsub hx.1, hx.2⟩
    · intro hsub
      exact D.fetta_mono
        (facePolytope_isFace_of P hB F.isFace F.subset_base) F.mem_vertex
        (facePolytope_isFace_of P hB G.isFace G.subset_base) G.mem_vertex
        hsub
  · -- map_dim
    intro F
    exact D.fetta_faceDim
      (facePolytope_isFace_of P hB F.isFace F.subset_base)
      F.mem_vertex F.dim_pos

/-! ## I corollari apicali, ora incondizionati -/

end LeanEval.Geometry.PlatonicClassification
-- Tengoku: root names of this library moved to Tengoku.LeanEvalPlatonicClassification so they do not collide with other libraries (generated)
