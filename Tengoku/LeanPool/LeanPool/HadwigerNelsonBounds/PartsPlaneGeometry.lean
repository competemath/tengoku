/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.HadwigerNelsonBounds.PartsCanonicalTriangle

/-!
# Plane geometry for the Parts spindle

This module gives an explicit triangular-lattice realization and elementary
distance-preserving rotations.  The two exact cosines are the angles used in
Parts' doubled wheel and spindle.
-/

@[expose] public section

namespace HadwigerNelsonBounds

/-- A point in `R²` from its two Cartesian coordinates. -/
noncomputable def pointR2 (x y : ℝ) : R2 :=
  WithLp.toLp 2 ![x, y]

/--
@isnad1 id=eq.0h2v.s6.36c5a54650ad from=translated src=- shape=02f1c7bf vocab=f4a6017e
-/
@[simp] lemma pointR2_zero (x y : ℝ) : pointR2 x y 0 = x := rfl
/--
@isnad1 id=eq.0h2v.s6.fec618709d32 from=translated src=- shape=6e7fa9ed vocab=f4a6017e
-/
@[simp] lemma pointR2_one (x y : ℝ) : pointR2 x y 1 = y := rfl

/-- The triangular-lattice point with axial coordinates `(q,r)`. -/
noncomputable def partsAxialPoint (q r : ℤ) : R2 :=
  pointR2 (((q : ℝ) - r) / 2)
    (((q : ℝ) + r) * Real.sqrt 3 / 2)

/--
@isnad1 id=eq.0h0v.s6.5a5c01e94f09 from=translated src=- shape=8640e5ff vocab=e4ea795b
-/
@[simp] lemma partsAxialPoint_zero : partsAxialPoint 0 0 = 0 := by
  ext i
  fin_cases i <;> simp [partsAxialPoint, pointR2]

/--
@isnad1 id=eq.0h4v.s6.e3f7d22fb68c from=translated src=- shape=d16bebcb vocab=c98dfa5a
-/
lemma partsAxialPoint_add (q r q' r' : ℤ) :
    partsAxialPoint (q + q') (r + r') =
      partsAxialPoint q r + partsAxialPoint q' r' := by
  ext i
  fin_cases i <;> simp [partsAxialPoint, pointR2] <;> ring

/--
@isnad1 id=eq.0h2v.s6.1adcbe69d923 from=translated src=- shape=2d168834 vocab=2a379497
-/
lemma partsAxialPoint_neg (q r : ℤ) :
    partsAxialPoint (-q) (-r) = -partsAxialPoint q r := by
  ext i
  fin_cases i <;> simp [partsAxialPoint, pointR2] <;> ring

/--
@isnad1 id=eq.0h4v.s6.373d36d15521 from=translated src=- shape=d16bebcb vocab=66d2c7ed
-/
lemma partsAxialPoint_sub (q r q' r' : ℤ) :
    partsAxialPoint (q - q') (r - r') =
      partsAxialPoint q r - partsAxialPoint q' r' := by
  ext i
  fin_cases i <;> simp [partsAxialPoint, pointR2] <;> ring

private lemma partsPoint_195 :
    partsPoint (195 : Fin 481) = ⟨6, 0, 6, 0⟩ := by decide

private lemma partsPoint_205 :
    partsPoint (205 : Fin 481) = ⟨6, 0, -6, 0⟩ := by decide

private lemma partsPoint_215 :
    partsPoint (215 : Fin 481) = ⟨-12, 0, 0, 0⟩ := by decide

/--
@isnad1 id=eq.0h0v.s3.3a1fd10bce8e from=translated src=- shape=7a1d0b68 vocab=bd588a14
-/
lemma partsTriangleA_eq_axial : partsTriangleA = partsAxialPoint 1 0 := by
  ext i
  fin_cases i
  · norm_num [partsTriangleA, partsPoint_195, PartsPoint.toR2,
      partsAxialPoint, pointR2]
  · have hsqrt : Real.sqrt 3 ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    simp [partsTriangleA, partsPoint_195, PartsPoint.toR2,
      partsAxialPoint, pointR2]
    field_simp [hsqrt]
    nlinarith [sqrt_three_mul_self]

/--
@isnad1 id=eq.0h0v.s4.d64a75bba057 from=translated src=- shape=c82f0652 vocab=d99411ed
-/
lemma partsTriangleB_eq_axial : partsTriangleB = partsAxialPoint 0 (-1) := by
  ext i
  fin_cases i
  · norm_num [partsTriangleB, partsPoint_205, PartsPoint.toR2,
      partsAxialPoint, pointR2]
  · have hsqrt : Real.sqrt 3 ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    simp [partsTriangleB, partsPoint_205, PartsPoint.toR2,
      partsAxialPoint, pointR2]
    field_simp [hsqrt]
    nlinarith [sqrt_three_mul_self]

/--
@isnad1 id=eq.0h0v.s4.3d60db81f369 from=translated src=- shape=a8d4d362 vocab=fca4a248
-/
lemma partsTriangleC_eq_axial : partsTriangleC = partsAxialPoint (-1) 1 := by
  ext i
  fin_cases i
  · norm_num [partsTriangleC, partsPoint_215, PartsPoint.toR2,
      partsAxialPoint, pointR2]
  · norm_num [partsTriangleC, partsPoint_215, PartsPoint.toR2,
      partsAxialPoint, pointR2]

/-- Squared distance on the axial triangular lattice.
@isnad1 id=eq.0h4v.s7.d4f90a74fc80 from=translated src=- shape=f2aec516 vocab=2a7a1bfe
-/
lemma partsAxialPoint_dist_sq (q r q' r' : ℤ) :
    dist (partsAxialPoint q r) (partsAxialPoint q' r') ^ 2 =
      ((q - q' : ℤ) : ℝ) ^ 2 +
        ((q - q' : ℤ) : ℝ) * ((r - r' : ℤ) : ℝ) +
        ((r - r' : ℤ) : ℝ) ^ 2 := by
  rw [PiLp.dist_sq_eq_of_L2]
  simp only [Fin.sum_univ_two, partsAxialPoint, pointR2_zero, pointR2_one,
    Real.dist_eq, sq_abs, Int.cast_sub]
  have hsqrt : Real.sqrt 3 * Real.sqrt 3 = 3 := sqrt_three_mul_self
  ring_nf
  rw [show Real.sqrt 3 ^ 2 = 3 by nlinarith]
  ring

/--
@isnad1 id=eq.1h4v.s7.f22f920031a7 from=translated src=- shape=10fcfc8a vocab=c3619f97
-/
lemma partsAxialPoint_dist_eq_one {q r q' r' : ℤ}
    (hnorm : (q - q') ^ 2 + (q - q') * (r - r') + (r - r') ^ 2 = 1) :
    dist (partsAxialPoint q r) (partsAxialPoint q' r') = 1 := by
  have hsq : dist (partsAxialPoint q r) (partsAxialPoint q' r') ^ 2 = 1 := by
    rw [partsAxialPoint_dist_sq]
    exact_mod_cast hnorm
  have hnonneg : 0 ≤ dist (partsAxialPoint q r) (partsAxialPoint q' r') :=
    dist_nonneg
  nlinarith

/-- Rotation through an angle represented by its cosine and sine. -/
noncomputable def planeRotation (cosine sine : ℝ) (p : R2) : R2 :=
  pointR2 (cosine * p 0 - sine * p 1)
    (sine * p 0 + cosine * p 1)

/--
@isnad1 id=eq.0h2v.s7.fbb0b7491fc6 from=translated src=- shape=e740efd1 vocab=65abfec8
-/
@[simp] lemma planeRotation_zero (cosine sine : ℝ) :
    planeRotation cosine sine 0 = 0 := by
  ext i
  fin_cases i <;> simp [planeRotation, pointR2]

/--
@isnad1 id=eq.1h4v.s7.2d1fd1b0f8a2 from=translated src=- shape=69bc844f vocab=efd3852d
-/
lemma planeRotation_dist_eq {cosine sine : ℝ}
    (htrig : cosine ^ 2 + sine ^ 2 = 1) (p q : R2) :
    dist (planeRotation cosine sine p) (planeRotation cosine sine q) =
      dist p q := by
  have hsq :
      dist (planeRotation cosine sine p) (planeRotation cosine sine q) ^ 2 =
        dist p q ^ 2 := by
    rw [PiLp.dist_sq_eq_of_L2, PiLp.dist_sq_eq_of_L2]
    simp only [Fin.sum_univ_two, planeRotation, pointR2_zero, pointR2_one,
      Real.dist_eq, sq_abs]
    nlinarith [sq_nonneg (p 0 - q 0), sq_nonneg (p 1 - q 1)]
  have hleft : 0 ≤
      dist (planeRotation cosine sine p) (planeRotation cosine sine q) :=
    dist_nonneg
  have hright : 0 ≤ dist p q := dist_nonneg
  nlinarith

/--
@isnad1 id=eq.1h3v.s8.5d029e899a2a from=translated src=- shape=ae98749a vocab=d76ab2d9
-/
lemma planeRotation_displacement_sq {cosine sine : ℝ}
    (htrig : cosine ^ 2 + sine ^ 2 = 1) (p : R2) :
    dist p (planeRotation cosine sine p) ^ 2 =
      2 * (1 - cosine) * dist p 0 ^ 2 := by
  rw [PiLp.dist_sq_eq_of_L2, PiLp.dist_sq_eq_of_L2]
  simp [Fin.sum_univ_two, planeRotation, pointR2, Real.dist_eq, sq_abs]
  nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]

/-- The doubled-wheel angle has cosine `7/8`. -/
noncomputable def partsPatchCosine : ℝ := 7 / 8

/-- Positive sine of the doubled-wheel angle. -/
noncomputable def partsPatchSine : ℝ := Real.sqrt 15 / 8

/--
@isnad1 id=eq.0h0v.s5.b32dfad07267 from=translated src=- shape=5b64a77a vocab=401bfcf9
-/
lemma partsPatch_trig : partsPatchCosine ^ 2 + partsPatchSine ^ 2 = 1 := by
  have hsqrt : Real.sqrt 15 ^ 2 = 15 := Real.sq_sqrt (by norm_num)
  rw [partsPatchCosine, partsPatchSine]
  nlinarith

/-- Rotation used to superimpose the second triangular-lattice patch. -/
noncomputable def partsPatchRotation : R2 → R2 :=
  planeRotation partsPatchCosine partsPatchSine

/--
@isnad1 id=eq.0h2v.s6.aeef94190920 from=translated src=- shape=522be556 vocab=73df9262
-/
lemma partsPatchRotation_dist_eq (p q : R2) :
    dist (partsPatchRotation p) (partsPatchRotation q) = dist p q :=
  planeRotation_dist_eq partsPatch_trig p q

/--
@isnad1 id=eq.0h1v.s7.775421ce1597 from=translated src=- shape=f8f0aede vocab=3bccd3de
-/
lemma partsPatchRotation_displacement_sq (p : R2) :
    dist p (partsPatchRotation p) ^ 2 = dist p 0 ^ 2 / 4 := by
  rw [partsPatchRotation, planeRotation_displacement_sq partsPatch_trig,
    partsPatchCosine]
  ring

/--
@isnad1 id=eq.0h0v.s7.04cc6308c0a4 from=translated src=- shape=3c26ae4f vocab=a8b82ec5
-/
@[simp] lemma partsPatchRotation_zero : partsPatchRotation 0 = 0 :=
  planeRotation_zero _ _

/-- Apply the doubled-wheel rotation exactly when selecting its second patch. -/
noncomputable def partsApplyPatch (rotated : Bool) (p : R2) : R2 :=
  if rotated then partsPatchRotation p else p

/--
@isnad1 id=eq.0h3v.s6.394cadc4abf1 from=translated src=- shape=d1101c6f vocab=ac8ad9b7
-/
lemma partsApplyPatch_dist_eq (rotated : Bool) (p q : R2) :
    dist (partsApplyPatch rotated p) (partsApplyPatch rotated q) = dist p q := by
  cases rotated <;> simp [partsApplyPatch, partsPatchRotation_dist_eq]

/--
@isnad1 id=eq.0h1v.s7.6a37d551f461 from=translated src=- shape=9b4d794a vocab=ccee98ef
-/
@[simp] lemma partsApplyPatch_zero (rotated : Bool) :
    partsApplyPatch rotated 0 = 0 := by
  cases rotated <;> simp [partsApplyPatch]

/-- Optionally apply the central inversion used by a triangle witness. -/
def partsApplyNegation (negated : Bool) (p : R2) : R2 :=
  if negated then -p else p

/--
@isnad1 id=eq.0h3v.s6.69a3714ec591 from=translated src=- shape=d1101c6f vocab=153e7a1f
-/
lemma partsApplyNegation_dist_eq (negated : Bool) (p q : R2) :
    dist (partsApplyNegation negated p) (partsApplyNegation negated q) =
      dist p q := by
  cases negated <;> simp [partsApplyNegation]

/-- Translate, optionally invert, and optionally rotate a canonical triangle. -/
noncomputable def partsTriangleMotion (rotated : Bool) (centerQ centerR : ℤ)
    (negated : Bool) (p : R2) : R2 :=
  partsApplyPatch rotated
    (partsAxialPoint centerQ centerR + partsApplyNegation negated p)

/--
@isnad1 id=eq.0h6v.s6.53ba79fa112a from=translated src=- shape=64467714 vocab=3bc8fd7d
-/
lemma partsTriangleMotion_dist_eq (rotated : Bool) (centerQ centerR : ℤ)
    (negated : Bool) (p q : R2) :
    dist (partsTriangleMotion rotated centerQ centerR negated p)
        (partsTriangleMotion rotated centerQ centerR negated q) = dist p q := by
  rw [partsTriangleMotion, partsTriangleMotion, partsApplyPatch_dist_eq,
    dist_add_left, partsApplyNegation_dist_eq]

/--
@isnad1 id=eq.0h4v.s5.c1b53b034a26 from=translated src=- shape=f54f3be3 vocab=c175dc09
-/
lemma partsTriangleMotion_A (rotated : Bool) (centerQ centerR : ℤ)
    (negated : Bool) :
    partsTriangleMotion rotated centerQ centerR negated partsTriangleA =
      partsApplyPatch rotated
        (partsAxialPoint
          (centerQ + if negated then -1 else 1) centerR) := by
  rw [partsTriangleMotion, partsTriangleA_eq_axial]
  apply congrArg (partsApplyPatch rotated)
  cases negated <;>
    ext i <;> fin_cases i <;>
      simp [partsApplyNegation, partsAxialPoint, pointR2] <;> ring

/--
@isnad1 id=eq.0h4v.s5.b575127bffaf from=translated src=- shape=1b35fb1a vocab=878f0e8a
-/
lemma partsTriangleMotion_B (rotated : Bool) (centerQ centerR : ℤ)
    (negated : Bool) :
    partsTriangleMotion rotated centerQ centerR negated partsTriangleB =
      partsApplyPatch rotated
        (partsAxialPoint centerQ
          (centerR + if negated then 1 else -1)) := by
  rw [partsTriangleMotion, partsTriangleB_eq_axial]
  apply congrArg (partsApplyPatch rotated)
  cases negated <;>
    ext i <;> fin_cases i <;>
      simp [partsApplyNegation, partsAxialPoint, pointR2] <;> ring

/--
@isnad1 id=eq.0h4v.s6.06677032ca2f from=translated src=- shape=33450731 vocab=1ee2d075
-/
lemma partsTriangleMotion_C (rotated : Bool) (centerQ centerR : ℤ)
    (negated : Bool) :
    partsTriangleMotion rotated centerQ centerR negated partsTriangleC =
      partsApplyPatch rotated
        (partsAxialPoint
          (centerQ + if negated then 1 else -1)
          (centerR + if negated then -1 else 1)) := by
  rw [partsTriangleMotion, partsTriangleC_eq_axial]
  apply congrArg (partsApplyPatch rotated)
  cases negated <;>
    ext i <;> fin_cases i <;>
      simp [partsApplyNegation, partsAxialPoint, pointR2] <;> ring

/-- Pull a proper plane coloring back along any distance-preserving map. -/
noncomputable def pullbackUnitDistanceColoring {color : Type*}
    (planeColoring : unitDistanceGraph.Coloring color) (motion : R2 → R2)
    (hdist : ∀ p q, dist (motion p) (motion q) = dist p q) :
    unitDistanceGraph.Coloring color :=
  SimpleGraph.Coloring.mk (fun p => planeColoring (motion p)) (by
    intro p q hadj
    apply planeColoring.valid
    rw [unitDistanceGraph_adj] at hadj ⊢
    have hpq : dist p q = 1 := hadj.2.elim id (fun h => by
      rw [dist_comm]
      exact h)
    constructor
    · intro heq
      have hzero : dist (motion p) (motion q) = 0 := by
        rw [heq]
        exact dist_self _
      rw [hdist] at hzero
      linarith
    · left
      rw [hdist]
      exact hpq)

/--
@isnad1 id=eq.1h4v.s7.955406ddfff0 from=translated src=- shape=f3b0a423 vocab=b0a45434
-/
@[simp] lemma pullbackUnitDistanceColoring_apply {color : Type*}
    (planeColoring : unitDistanceGraph.Coloring color) (motion : R2 → R2)
    (hdist : ∀ p q, dist (motion p) (motion q) = dist p q) (p : R2) :
    pullbackUnitDistanceColoring planeColoring motion hdist p =
      planeColoring (motion p) := rfl

/-- Every rigid image of the checked canonical triangle is non-monochromatic.
@isnad1 id=not.0h5v.s7.8fa749d72399 from=translated src=- shape=1526cafe vocab=f0c77d22
-/
theorem parts_triangle_motion_not_monochromatic
    (planeColoring : unitDistanceGraph.Coloring (Fin 4))
    (rotated : Bool) (centerQ centerR : ℤ) (negated : Bool) :
    ¬(planeColoring
          (partsTriangleMotion rotated centerQ centerR negated partsTriangleA) =
        planeColoring
          (partsTriangleMotion rotated centerQ centerR negated partsTriangleB) ∧
      planeColoring
          (partsTriangleMotion rotated centerQ centerR negated partsTriangleB) =
        planeColoring
          (partsTriangleMotion rotated centerQ centerR negated partsTriangleC)) := by
  let motion := partsTriangleMotion rotated centerQ centerR negated
  let pulled : unitDistanceGraph.Coloring (Fin 4) :=
    SimpleGraph.Coloring.mk (fun p => planeColoring (motion p)) (by
      intro p q hadj
      apply planeColoring.valid
      rw [unitDistanceGraph_adj] at hadj ⊢
      have hpq : dist p q = 1 := hadj.2.elim id (fun h => by
        rw [dist_comm]
        exact h)
      constructor
      · intro heq
        have hzero : dist (motion p) (motion q) = 0 := by simp [heq]
        dsimp [motion] at hzero
        rw [partsTriangleMotion_dist_eq] at hzero
        linarith
      · left
        dsimp [motion]
        rw [partsTriangleMotion_dist_eq]
        exact hpq)
  intro hmono
  apply parts_canonical_triangle_not_monochromatic pulled
  change planeColoring (motion partsTriangleA) =
      planeColoring (motion partsTriangleB) ∧
    planeColoring (motion partsTriangleB) =
      planeColoring (motion partsTriangleC)
  simpa [motion] using hmono

/-- The final spindle angle has cosine `31/32`. -/
noncomputable def partsSpindleCosine : ℝ := 31 / 32

/-- Positive sine of the final spindle angle. -/
noncomputable def partsSpindleSine : ℝ := Real.sqrt 63 / 32

/--
@isnad1 id=eq.0h0v.s5.63611de7a9a9 from=translated src=- shape=5b64a77a vocab=b9d0d7bd
-/
lemma partsSpindle_trig :
    partsSpindleCosine ^ 2 + partsSpindleSine ^ 2 = 1 := by
  have hsqrt : Real.sqrt 63 ^ 2 = 63 := Real.sq_sqrt (by norm_num)
  rw [partsSpindleCosine, partsSpindleSine]
  nlinarith

/-- Rotation used to close the final spindle. -/
noncomputable def partsSpindleRotation : R2 → R2 :=
  planeRotation partsSpindleCosine partsSpindleSine

/--
@isnad1 id=eq.0h2v.s6.abb57a272822 from=translated src=- shape=522be556 vocab=cbeace83
-/
lemma partsSpindleRotation_dist_eq (p q : R2) :
    dist (partsSpindleRotation p) (partsSpindleRotation q) = dist p q :=
  planeRotation_dist_eq partsSpindle_trig p q

/--
@isnad1 id=eq.0h1v.s7.87cf81880965 from=translated src=- shape=f8f0aede vocab=967e7d85
-/
lemma partsSpindleRotation_displacement_sq (p : R2) :
    dist p (partsSpindleRotation p) ^ 2 = dist p 0 ^ 2 / 16 := by
  rw [partsSpindleRotation, planeRotation_displacement_sq partsSpindle_trig,
    partsSpindleCosine]
  ring

/--
@isnad1 id=eq.0h0v.s7.ea2ed15495e7 from=translated src=- shape=3c26ae4f vocab=0159640b
-/
@[simp] lemma partsSpindleRotation_zero : partsSpindleRotation 0 = 0 :=
  planeRotation_zero _ _

end HadwigerNelsonBounds
