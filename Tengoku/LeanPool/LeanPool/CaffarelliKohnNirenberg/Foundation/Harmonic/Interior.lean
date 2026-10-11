/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.NewtonianRepresentation
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorBasic
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Pressure.Cutoff
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import Tengoku

/-!
# Interior

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic

/-!
# Harmonic interior estimates from the Newtonian representation

Kernel and integration-by-parts infrastructure for the representation route.
-/
noncomputable section

namespace CKN.Foundation.Heat

theorem newtonianKernel_spatialDeriv_size_bound {z : Vec3} (hz : z ≠ 0)
    (i : Fin 3) :
    |CKN.spatialDeriv newtonianKernel i z| ≤ (4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹ := by
  have hdirect := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (CKN.basisVec i))
    (hasFDerivAt_newtonianKernel hz).fderiv
  change CKN.spatialDeriv newtonianKernel i z = _ at hdirect
  have hformula : CKN.spatialDeriv newtonianKernel i z =
      -(4 * Real.pi)⁻¹ * z i * q z ^ (-(3 : ℝ) / 2) := by
    convert hdirect using 1
    simp [smul_eq_mul, CKN.basisVec_apply]
    ring_nf
  have hr : 0 < vec3EuclideanNorm z := by
    rw [vec3EuclideanNorm_eq_l2, norm_pos_iff]
    intro hzero
    exact hz ((WithLp.toLp_eq_zero 2).mp hzero)
  have hq : q z = vec3EuclideanNorm z ^ 2 := q_eq_vec3Norm_sq z
  have hqi : q z ^ (-(3 : ℝ) / 2) =
      (vec3EuclideanNorm z) ^ (-(3 : ℝ)) := by
    rw [hq, show (-(3 : ℝ) / 2) = -(3 / 2 : ℝ) by ring,
      show vec3EuclideanNorm z ^ 2 = vec3EuclideanNorm z ^ (2 : ℝ) by norm_num,
      ← Real.rpow_mul (vec3EuclideanNorm_nonneg z)]
    congr 1
    ring
  have hcoord : |z i| ≤ vec3EuclideanNorm z := by
    simpa [CKN.vecEuclideanNorm, CKN.vecNormSq, CKN.vecDot,
      vec3EuclideanNorm, pow_two] using CKN.abs_apply_le_vecEuclideanNorm z i
  rw [hformula]
  have habs : |-(4 * Real.pi)⁻¹ * z i * q z ^ (-(3 : ℝ) / 2)| =
      (4 * Real.pi)⁻¹ * |z i| * q z ^ (-(3 : ℝ) / 2) := by
    rw [show -(4 * Real.pi)⁻¹ * z i * q z ^ (-(3 : ℝ) / 2) =
        -((4 * Real.pi)⁻¹ * z i * q z ^ (-(3 : ℝ) / 2)) by ring,
      abs_neg, abs_mul, abs_mul, abs_of_nonneg (by positivity),
      abs_of_nonneg (Real.rpow_nonneg (q_pos hz).le _)]
  rw [habs, hqi]
  have hpow : vec3EuclideanNorm z * vec3EuclideanNorm z ^ (-(3 : ℝ)) =
      vec3EuclideanNorm z ^ (-(2 : ℝ)) := by
    calc
      vec3EuclideanNorm z * vec3EuclideanNorm z ^ (-(3 : ℝ)) =
          vec3EuclideanNorm z ^ (1 : ℝ) *
            vec3EuclideanNorm z ^ (-(3 : ℝ)) := by rw [Real.rpow_one]
      _ = vec3EuclideanNorm z ^ ((1 : ℝ) + (-(3 : ℝ))) := by
        rw [← Real.rpow_add hr]
      _ = vec3EuclideanNorm z ^ (-(2 : ℝ)) := by norm_num
  calc
    (4 * Real.pi)⁻¹ * |z i| * vec3EuclideanNorm z ^ (-(3 : ℝ)) ≤
        (4 * Real.pi)⁻¹ * vec3EuclideanNorm z *
          vec3EuclideanNorm z ^ (-(3 : ℝ)) := by
      gcongr
    _ = (4 * Real.pi)⁻¹ * vec3EuclideanNorm z ^ (-(2 : ℝ)) := by
      rw [show (4 * Real.pi)⁻¹ * vec3EuclideanNorm z *
          vec3EuclideanNorm z ^ (-(3 : ℝ)) =
          (4 * Real.pi)⁻¹ *
            (vec3EuclideanNorm z * vec3EuclideanNorm z ^ (-(3 : ℝ))) by ring,
        hpow]
    _ ≤ (4 * Real.pi)⁻¹ * ‖z‖ ^ (-(2 : ℝ)) := by
      have hspace : ‖z‖ ≤ vec3EuclideanNorm z := by
        simpa [CKN.vecEuclideanNorm, CKN.vecNormSq, CKN.vecDot,
          CKN.spaceEuclideanNorm, vec3EuclideanNorm, pow_two] using
          CKN.space_norm_le_euclideanNorm z
      have hinv : (vec3EuclideanNorm z) ^ (-(2 : ℝ)) ≤ ‖z‖ ^ (-(2 : ℝ)) := by
        rw [Real.rpow_neg (vec3EuclideanNorm_nonneg _),
          Real.rpow_neg (norm_nonneg _)]
        apply (inv_le_inv₀ (by positivity) (by positivity)).2
        rw [Real.rpow_two, Real.rpow_two]
        exact (sq_le_sq₀ (norm_nonneg _) (vec3EuclideanNorm_nonneg _)).2 hspace
      exact mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = (4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹ := by
      rw [show (-(2 : ℝ)) = -(2 : ℝ) by norm_num,
        Real.rpow_neg (norm_nonneg _), Real.rpow_two]

theorem spatialDeriv_newtonianKernel_shift_eq_neg
    {x y : Vec3} (hxy : x - y ≠ 0) (i : Fin 3) :
    CKN.spatialDeriv (fun z : Vec3 => newtonianKernel (x - z)) i y =
      -CKN.spatialDeriv newtonianKernel i (x - y) := by
  rw [spatialDeriv_newtonianKernel_shift hxy]
  have hdirect := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (CKN.basisVec i))
    (hasFDerivAt_newtonianKernel hxy).fderiv
  change CKN.spatialDeriv newtonianKernel i (x - y) = _ at hdirect
  rw [hdirect]
  simp [smul_eq_mul, CKN.basisVec_apply]
  ring_nf

theorem spatialDeriv_kernelCutoffDerivative_at_x
    {x x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (13 * ρ / 20)) (i j : Fin 3) :
    CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) j x = 0 := by
  have heq : kernelCutoffDerivative x x₀ hρ i =ᶠ[𝓝 x]
      (fun _ : Vec3 => (0 : ℝ)) := by
    exact spatialDeriv_eta_eventually_zero x x₀ hρ hx i |>.mono fun z hz => by
      simp [kernelCutoffDerivative, hz]
  have hfd := heq.fderiv_eq (𝕜 := ℝ)
  change (fderiv ℝ (kernelCutoffDerivative x x₀ hρ i) x)
      (CKN.basisVec j) = 0
  rw [hfd]
  simp

theorem spatialDeriv_kernelCutoffDerivative_of_ne
    {x x₀ y : Vec3} {ρ : ℝ} (hρ : 0 < ρ) (hxy : x - y ≠ 0)
    (i j : Fin 3) :
    CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) j y =
      CKN.spatialDeriv (fun z : Vec3 => newtonianKernel (x - z)) j y *
          CKN.spatialDeriv (eta x₀ hρ) i y +
        newtonianKernel (x - y) *
          CKN.spatialDeriv (CKN.spatialDeriv (eta x₀ hρ) i) j y := by
  have hsub : HasFDerivAt (fun z : Vec3 => x - z)
      (-ContinuousLinearMap.id ℝ Vec3) y := by
    simpa using (hasFDerivAt_const (𝕜 := ℝ) x y).sub
      (hasFDerivAt_id (𝕜 := ℝ) y)
  have hkernel := (hasFDerivAt_newtonianKernel hxy).comp y hsub
  have heta0 : ContDiff ℝ (↑(⊤ : ℕ∞)) (eta x₀ hρ) := by
    simpa only [eta] using mollifiedBallCutoff_smooth x₀ hρ
  have heta_diff : DifferentiableAt ℝ
      (CKN.spatialDeriv (eta x₀ hρ) i) y :=
    (contDiff_spatialDeriv_two heta0 i).differentiable (by norm_num) y
  have hrule := CKN.spatialDeriv_mul hkernel.differentiableAt heta_diff j
  change CKN.spatialDeriv (fun z : Vec3 => newtonianKernel (x - z) *
      CKN.spatialDeriv (eta x₀ hρ) i z) j y = _
  simpa only [Function.comp_def] using hrule

theorem kernelCutoffDerivative_contDiff_one (x x₀ : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (hx : x ∈ euclideanBall x₀ (13 * ρ / 20)) (i : Fin 3) :
    ContDiff ℝ (1 : ℕ) (kernelCutoffDerivative x x₀ hρ i) := by
  exact kernelCutoffDerivative_contDiff x x₀ hρ hx i

theorem kernelCutoffDerivative_hasCompactSupport_global (x x₀ : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (i : Fin 3) :
    HasCompactSupport (kernelCutoffDerivative x x₀ hρ i) := by
  exact kernelCutoffDerivative_hasCompactSupport x x₀ hρ i

theorem kernelCutoffDerivative_integrable_mul_right_global
    {h : Vec3 → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (x x₀ : Vec3)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (13 * ρ / 20)) (i : Fin 3) :
    Integrable (fun y : Vec3 =>
      h y * CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y)
      volume := by
  exact kernelCutoffDerivative_integrable_mul_right hh x x₀ hρ hx i

theorem eta_spatialDeriv_contDiff_two_global (x₀ : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (i : Fin 3) :
    ContDiff ℝ (2 : ℕ) (spatialDeriv (eta x₀ hρ) i) := by
  exact contDiff_spatialDeriv_two
    (by simpa only [eta] using mollifiedBallCutoff_smooth x₀ hρ) i

theorem eta_spatialSecond_continuous_global (x₀ : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (i : Fin 3) :
    Continuous (spatialDeriv (spatialDeriv (eta x₀ hρ) i) i) := by
  exact (eta_spatialDeriv_contDiff_two_global x₀ hρ i).continuous_fderiv
    (by norm_num) |>.clm_apply continuous_const

end CKN.Foundation.Heat
