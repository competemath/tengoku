/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.HadwigerNelsonBounds.PartsGadgetCertificate
public import Tengoku.LeanPool.LeanPool.HadwigerNelsonBounds.PartsGadgetEmbeddingCore
import Tengoku.LeanPool.LeanPool.HadwigerNelsonBounds.PartsGadgetEdgeVerification
import Tengoku.LeanPool.LeanPool.HadwigerNelsonBounds.PartsGadgetForcedPair
import Tengoku.LeanPool.LeanPool.HadwigerNelsonBounds.PartsGadgetSymmetry

/-!
# The finite Parts gadget inside the unit-distance plane

Every combinatorial edge is a unit segment and every hyperedge is a rigid copy
of the canonical triangle ruled out by the checked 481-vertex certificate.
-/

@[expose] public section

namespace HadwigerNelsonBounds

/-- Restrict a plane coloring to the 73 explicit gadget points. -/
noncomputable def partsGadgetColoring
    (planeColoring : unitDistanceGraph.Coloring (Fin 4)) : Fin 73 → Fin 4 :=
  fun vertex => planeColoring (partsGadgetPoint vertex)

/--
@isnad1 id=partsgad.0h1v.s3.c4c9b7711866 from=translated src=- shape=83bedc8d vocab=8adf7e17
-/
lemma partsGadgetColoring_valid
    (planeColoring : unitDistanceGraph.Coloring (Fin 4)) :
    PartsGadgetValid (partsGadgetColoring planeColoring) := by
  constructor
  · intro vertex neighbor hadj heq
    have hdist : dist (partsGadgetPoint vertex)
        (partsGadgetPoint neighbor) = 1 :=
      partsGadgetPoint_dist_eq_one_of_edgeCase (partsGadget_edgeCase hadj)
    have hadjPlane : unitDistanceGraph.Adj (partsGadgetPoint vertex)
        (partsGadgetPoint neighbor) := by
      rw [unitDistanceGraph_adj]
      constructor
      · intro hpoints
        have hzero : dist (partsGadgetPoint vertex)
            (partsGadgetPoint neighbor) = 0 := by
          rw [hpoints]
          exact dist_self _
        linarith
      · exact Or.inl hdist
    exact planeColoring.valid hadjPlane heq
  · intro vertex pair hpair hmono
    rw [partsGadgetTriplePairs, List.mem_map] at hpair
    rcases hpair with ⟨witness, hwitness, rfl⟩
    have hvalid := partsGadgetTriangleWitness_valid hwitness
    apply partsGadgetWitness_roles_not_monochromatic planeColoring hvalid
    apply partsGadget_monochromatic_of_sameTriple
      (partsGadgetColoring planeColoring) hvalid.1
    exact hmono

/-- The explicitly embedded doubled patch forces its opposite endpoints to
have equal colors in every proper four-coloring of the plane.
@isnad1 id=eq.0h1v.s7.31e230a98346 from=translated src=- shape=ed55c540 vocab=30c07c8e
-/
theorem parts_doubled_patch_forces_monochromatic_pair
    (planeColoring : unitDistanceGraph.Coloring (Fin 4)) :
    planeColoring (partsGadgetPoint 5) =
      planeColoring (partsGadgetPoint 31) := by
  exact parts_gadget_forces_monochromatic_pair
    (partsGadgetColoring_valid planeColoring)

/--
@isnad1 id=eq.0h0v.s5.1b0dacc5fffc from=translated src=- shape=f942bd63 vocab=f26c423f
-/
lemma partsGadgetPoint_five :
    partsGadgetPoint 5 = partsAxialPoint (-2) 0 := by
  rfl

/--
@isnad1 id=eq.0h0v.s4.7a65cced941a from=translated src=- shape=7bd9679a vocab=9209994e
-/
lemma partsGadgetPoint_thirtyOne :
    partsGadgetPoint 31 = partsAxialPoint 2 0 := by
  rfl

/-- The forced pair in axial coordinates; its Euclidean distance is four.
@isnad1 id=eq.0h1v.s7.16f30d74f64f from=translated src=- shape=f2f04317 vocab=9184b7c1
-/
theorem parts_axial_pair_forces_monochromatic
    (planeColoring : unitDistanceGraph.Coloring (Fin 4)) :
    planeColoring (partsAxialPoint (-2) 0) =
      planeColoring (partsAxialPoint 2 0) := by
  simpa [partsGadgetPoint_five, partsGadgetPoint_thirtyOne] using
    parts_doubled_patch_forces_monochromatic_pair planeColoring

/-- Every distance-preserving image of the doubled patch forces the
corresponding distance-four pair to be monochromatic.
@isnad1 id=eq.1h2v.s7.24d6db02985f from=translated src=- shape=214ac59a vocab=a9190aac
-/
theorem parts_axial_pair_forces_under_motion
    (planeColoring : unitDistanceGraph.Coloring (Fin 4)) (motion : R2 → R2)
    (hdist : ∀ p q, dist (motion p) (motion q) = dist p q) :
    planeColoring (motion (partsAxialPoint (-2) 0)) =
      planeColoring (motion (partsAxialPoint 2 0)) := by
  let pulled := pullbackUnitDistanceColoring planeColoring motion hdist
  have hforced := parts_axial_pair_forces_monochromatic pulled
  simpa [pulled] using hforced

end HadwigerNelsonBounds
