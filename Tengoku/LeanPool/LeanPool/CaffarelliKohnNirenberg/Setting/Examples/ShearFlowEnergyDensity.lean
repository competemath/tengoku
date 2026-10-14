/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.Examples.ShearFlow

/-! # Pointwise energy calculus for the viscous shear -/

@[expose] public section

open MeasureTheory Set
open CKN.Foundation.Parabolic
open CKN.ShearCalculus

namespace CKN

/-- The kinetic-energy density of the shear. -/
noncomputable def shearEnergy (z : Vec3 × ℝ) : ℝ := shearAmplitude z * shearAmplitude z

/-- The cubic scalar transport factor. -/
noncomputable def shearTransport (z : Vec3 × ℝ) : ℝ := shearEnergy z * shearAmplitude z

/-- Smoothness of the energy density.
@isnad1 id=contdiff.0h0v.s7.24b24beac54b from=translated src=- shape=7c29c6d3 vocab=595dc180
-/
theorem shearEnergy_smooth : ContDiff ℝ (⊤ : ℕ∞) shearEnergy :=
  shearAmplitude_smooth.mul shearAmplitude_smooth

/-- Smoothness of the cubic transport factor.
@isnad1 id=contdiff.0h0v.s7.a320ae4ba8e3 from=translated src=- shape=7c29c6d3 vocab=69b0ac6b
-/
theorem shearTransport_smooth : ContDiff ℝ (⊤ : ℕ∞) shearTransport :=
  shearEnergy_smooth.mul shearAmplitude_smooth

/-- The energy has no derivative along the flow direction.
@isnad1 id=eq.0h2v.s6.7d26121deb75 from=translated src=- shape=c73033f7 vocab=03a24503
-/
theorem shearEnergy_spatial (z : Vec3 × ℝ) (j : Fin 3) :
    spatialPartial shearEnergy j z =
      if j = 1 then 2 * (shearAmplitude z * shearSlope z) else 0 := by
  change spatialPartial (fun w : Vec3 × ℝ => shearAmplitude w * shearAmplitude w) j z = _
  rw [spatial_mul shearAmplitude_smooth shearAmplitude_smooth]
  rw [shearAmplitude_spatial]
  by_cases hj : j = 1
  · simp only [hj, ite_true]
    ring
  · simp [hj]

/-- Time derivative of the energy density.
@isnad1 id=eq.0h1v.s4.561f84dd1cf2 from=translated src=- shape=65589053 vocab=8c2e58f3
-/
theorem shearEnergy_time (z : Vec3 × ℝ) :
    timePartial shearEnergy z = -2 * shearEnergy z := by
  change timePartial (fun w : Vec3 × ℝ => shearAmplitude w * shearAmplitude w) z = _
  rw [time_mul shearAmplitude_smooth shearAmplitude_smooth, shearAmplitude_time]
  unfold shearEnergy
  ring

/-- The cubic transport also has zero flow-direction derivative.
@isnad1 id=eq.0h1v.s4.64aa81c5007a from=translated src=- shape=2d50a8b0 vocab=93f4b837
-/
theorem shearTransport_spatial_zero (z : Vec3 × ℝ) :
    spatialPartial shearTransport 0 z = 0 := by
  change spatialPartial (fun w : Vec3 × ℝ => shearEnergy w * shearAmplitude w) 0 z = _
  rw [spatial_mul shearEnergy_smooth shearAmplitude_smooth,
    shearEnergy_spatial, shearAmplitude_spatial]
  norm_num

/-- Second spatial derivatives of the energy density.
@isnad1 id=eq.0h2v.s6.04b043b551e4 from=translated src=- shape=fd62d4a8 vocab=9eeea5be
-/
theorem shearEnergy_second (z : Vec3 × ℝ) (j : Fin 3) :
    spatialPartial (fun w : Vec3 × ℝ => spatialPartial shearEnergy j w) j z =
      if j = 1 then 2 * (shearSlope z * shearSlope z - shearEnergy z) else 0 := by
  have he : (fun w : Vec3 × ℝ => spatialPartial shearEnergy j w) =
      (fun w : Vec3 × ℝ => if j = 1 then 2 * (shearAmplitude w * shearSlope w) else 0) := by
    funext w
    exact shearEnergy_spatial w j
  rw [he]
  by_cases hj : j = 1
  · subst j
    simp only [ite_true]
    rw [spatial_mul contDiff_const (shearAmplitude_smooth.mul shearSlope_smooth),
      spatial_mul shearAmplitude_smooth shearSlope_smooth,
      shearAmplitude_spatial, shearSlope_spatial]
    simp only [spatialPartial, fderiv_const_apply, zero_apply, zero_mul,
      zero_add, ite_true]
    unfold shearEnergy
    ring
  · simp [hj, spatialPartial]

/-- The squared Euclidean speed is the scalar energy.
@isnad1 id=eq.0h1v.s4.bc948a5d591b from=translated src=- shape=d7195206 vocab=591b36db
-/
theorem shearFlow_energy (z : ParabolicPoint) :
    vec3EuclideanNorm (shearFlow z) ^ 2 = shearEnergy z := by
  unfold vec3EuclideanNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _hi => sq_nonneg _)]
  simp [shearFlow, shearEnergy, shearAmplitude, pow_two]

/-- The squared gradient density is the squared transverse slope.
@isnad1 id=eq.0h1v.s4.45216b1f4256 from=translated src=- shape=8f00d362 vocab=46584858
-/
theorem shearFlow_gradientSq (z : ParabolicPoint) :
    spatialGradientSq shearFlow shearFlowGrad z = shearSlope z * shearSlope z := by
  simp [spatialGradientSq, shearFlowGrad, Fin.sum_univ_three, shearSlope, pow_two]

end CKN
