/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.HadwigerNelsonBounds.PartsPlaneGeometry
import Tengoku.LeanPool.LeanPool.HadwigerNelsonBounds.IsbellColoring
import Tengoku.LeanPool.LeanPool.HadwigerNelsonBounds.PartsGadgetEmbedding

/-!
# The Parts spindle and the known bounds

Two copies of the forced distance-four pair share one endpoint.  Rotating the
second copy through cosine `31/32` makes the remaining endpoints unit-adjacent,
contradicting a proper four-coloring.
-/

@[expose] public section

namespace HadwigerNelsonBounds

/-- The distance-four vector between the translated gadget endpoints. -/
noncomputable def partsSpindleVector : R2 := partsAxialPoint 4 0

/-- Translate the first doubled patch so its left endpoint is the origin. -/
noncomputable def partsFirstSpindleMotion (p : R2) : R2 :=
  p - partsAxialPoint (-2) 0

/-- Translate the second doubled patch and rotate it around the shared origin. -/
noncomputable def partsSecondSpindleMotion (p : R2) : R2 :=
  partsSpindleRotation (p - partsAxialPoint (-2) 0)

/--
@isnad1 id=eq.0h2v.s6.1382d7654f5d from=translated src=- shape=522be556 vocab=92deae16
-/
lemma partsFirstSpindleMotion_dist_eq (p q : R2) :
    dist (partsFirstSpindleMotion p) (partsFirstSpindleMotion q) = dist p q := by
  simp [partsFirstSpindleMotion]

/--
@isnad1 id=eq.0h2v.s6.74af401344c4 from=translated src=- shape=522be556 vocab=71a373eb
-/
lemma partsSecondSpindleMotion_dist_eq (p q : R2) :
    dist (partsSecondSpindleMotion p) (partsSecondSpindleMotion q) = dist p q := by
  rw [partsSecondSpindleMotion, partsSecondSpindleMotion,
    partsSpindleRotation_dist_eq, dist_sub_right]

/--
@isnad1 id=eq.0h0v.s6.c2a9e6384a21 from=translated src=- shape=1377615d vocab=56a41d73
-/
@[simp] lemma partsFirstSpindleMotion_left :
    partsFirstSpindleMotion (partsAxialPoint (-2) 0) = 0 := by
  simp [partsFirstSpindleMotion]

/--
@isnad1 id=eq.0h0v.s3.1055cc064a1a from=translated src=- shape=6dd1337a vocab=8708cf24
-/
@[simp] lemma partsFirstSpindleMotion_right :
    partsFirstSpindleMotion (partsAxialPoint 2 0) = partsSpindleVector := by
  rw [partsFirstSpindleMotion, partsSpindleVector,
    ← partsAxialPoint_sub]
  norm_num

/--
@isnad1 id=eq.0h0v.s6.253eb84656dd from=translated src=- shape=1377615d vocab=c21e9cd3
-/
@[simp] lemma partsSecondSpindleMotion_left :
    partsSecondSpindleMotion (partsAxialPoint (-2) 0) = 0 := by
  simp [partsSecondSpindleMotion]

/--
@isnad1 id=eq.0h0v.s4.f0622442db2b from=translated src=- shape=5cb2c9f2 vocab=97a3bf74
-/
@[simp] lemma partsSecondSpindleMotion_right :
    partsSecondSpindleMotion (partsAxialPoint 2 0) =
      partsSpindleRotation partsSpindleVector := by
  rw [partsSecondSpindleMotion, partsSpindleVector,
    ← partsAxialPoint_sub]
  norm_num

/--
@isnad1 id=eq.0h0v.s7.3c1e91316d07 from=translated src=- shape=2cd2aab2 vocab=fc4b27d3
-/
lemma partsSpindleVector_norm_sq : dist partsSpindleVector 0 ^ 2 = 16 := by
  rw [partsSpindleVector, ← partsAxialPoint_zero,
    partsAxialPoint_dist_sq]
  norm_num

/-- The two free spindle endpoints are exactly one unit apart.
@isnad1 id=eq.0h0v.s5.b76b37450180 from=translated src=- shape=751351d3 vocab=c8632709
-/
lemma partsSpindleVector_rotated_dist :
    dist partsSpindleVector (partsSpindleRotation partsSpindleVector) = 1 := by
  have hsq :
      dist partsSpindleVector (partsSpindleRotation partsSpindleVector) ^ 2 =
        1 := by
    rw [partsSpindleRotation_displacement_sq, partsSpindleVector_norm_sq]
    norm_num
  have hnonneg : 0 ≤
      dist partsSpindleVector (partsSpindleRotation partsSpindleVector) :=
    dist_nonneg
  nlinarith

/-- **Parts lower bound.** The unit-distance graph of the Euclidean plane has
no proper coloring with four colors.
@isnad1 id=not.0h0v.s3.e330ef87f256 from=translated src=- shape=1aa9e057 vocab=58004257
-/
theorem unitDistanceGraph_not_colorable_four :
    ¬ unitDistanceGraph.Colorable 4 := by
  rintro ⟨planeColoring⟩
  have hfirst := parts_axial_pair_forces_under_motion planeColoring
    partsFirstSpindleMotion partsFirstSpindleMotion_dist_eq
  have hsecond := parts_axial_pair_forces_under_motion planeColoring
    partsSecondSpindleMotion partsSecondSpindleMotion_dist_eq
  simp only [partsFirstSpindleMotion_left, partsFirstSpindleMotion_right] at hfirst
  simp only [partsSecondSpindleMotion_left,
    partsSecondSpindleMotion_right] at hsecond
  have hsame : planeColoring partsSpindleVector =
      planeColoring (partsSpindleRotation partsSpindleVector) :=
    hfirst.symm.trans hsecond
  have hadj : unitDistanceGraph.Adj partsSpindleVector
      (partsSpindleRotation partsSpindleVector) := by
    rw [unitDistanceGraph_adj]
    constructor
    · intro hpoints
      have hzero : dist partsSpindleVector
          (partsSpindleRotation partsSpindleVector) = 0 := by
        exact dist_eq_zero.mpr hpoints
      linarith [partsSpindleVector_rotated_dist]
    · exact Or.inl partsSpindleVector_rotated_dist
  exact planeColoring.valid hadj hsame

/-- **Lower bound — `5 ≤ χ(ℝ²)`.**
@isnad1 id=le.0h0v.s3.f8fe2a6cd353 from=translated src=- shape=7164367e vocab=6031f7f7
-/
theorem five_le_chromaticNumber :
    (5 : ℕ∞) ≤ unitDistanceGraph.chromaticNumber := by
  apply SimpleGraph.le_chromaticNumber_iff_colorable.2
  intro colors hcolorable
  norm_cast
  by_contra hnot
  have hle : colors ≤ 4 := by omega
  exact unitDistanceGraph_not_colorable_four (hcolorable.mono hle)

end HadwigerNelsonBounds
