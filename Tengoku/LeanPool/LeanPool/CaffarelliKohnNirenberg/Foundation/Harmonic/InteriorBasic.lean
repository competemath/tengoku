/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.NewtonianRepresentation
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Pressure.Cutoff
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import Tengoku.Seed.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Deriv
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.NewtonianKernelIntegrability

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Interior Basic

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

/-- Squared Euclidean radius in native three-dimensional coordinates. -/
def q (z : Vec3) : ℝ := ∑ i : Fin 3, z i ^ 2

lemma q_pos {z : Vec3} (hz : z ≠ 0) : 0 < q z := by
  have hsum : q z = vec3EuclideanNorm z ^ 2 := by
    unfold q vec3EuclideanNorm
    rw [Real.sq_sqrt]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg (z i))
  rw [hsum]
  have : 0 < vec3EuclideanNorm z := by
    rw [vec3EuclideanNorm_eq_l2, norm_pos_iff]
    intro hzero
    apply hz
    exact (WithLp.toLp_eq_zero 2).mp hzero
  positivity

lemma q_eq_vec3Norm_sq (z : Vec3) :
    q z = vec3EuclideanNorm z ^ 2 := by
  unfold q vec3EuclideanNorm
  rw [Real.sq_sqrt]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (z i))

private lemma contDiff_q : ContDiff ℝ (⊤ : ℕ∞) q := by
  unfold q
  apply ContDiff.sum
  intro i hi
  exact (contDiff_apply ℝ ℝ i).pow 2

private lemma contDiffAt_newtonianKernel {z : Vec3} (hz : z ≠ 0) :
    ContDiffAt ℝ (2 : ℕ) newtonianKernel z := by
  have hqpos : q z ≠ 0 := (q_pos hz).ne'
  have hpow := (Real.contDiffAt_rpow_const (n := 2)
    (x := q z) (p := -(1 : ℝ) / 2) (Or.inl hqpos)).comp z
    (contDiff_q.contDiffAt.of_le (by norm_num))
  have hconst : ContDiffAt ℝ (2 : ℕ)
      (fun _ : Vec3 => (4 * Real.pi)⁻¹) z :=
    (contDiff_const : ContDiff ℝ (2 : ℕ) (fun _ : Vec3 => (4 * Real.pi)⁻¹)).contDiffAt
  have hmul := hconst.mul hpow
  have hkernel : (fun y : Vec3 => newtonianKernel y) =
      (fun y : Vec3 => (4 * Real.pi)⁻¹ * q y ^ (-(1 : ℝ) / 2)) := by
    funext y
    by_cases hy : y = 0
    · subst y
      simp [newtonianKernel, q, vec3EuclideanNorm]
    · rw [newtonianKernel, q_eq_vec3Norm_sq]
      rw [one_div]
      rw [show (4 * Real.pi * vec3EuclideanNorm y)⁻¹ =
          (4 * Real.pi)⁻¹ * (vec3EuclideanNorm y)⁻¹ by ring]
      rw [show -(1 : ℝ) / 2 = -(1 / 2 : ℝ) by ring,
        Real.rpow_neg (sq_nonneg (vec3EuclideanNorm y))]
      have hsqrt : (vec3EuclideanNorm y ^ 2) ^ (1 / 2 : ℝ) =
          vec3EuclideanNorm y := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs,
          abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
      rw [hsqrt]
  change ContDiffAt ℝ (2 : ℕ) (fun y : Vec3 => newtonianKernel y) z
  rw [hkernel]
  simpa only [Function.comp_apply] using hmul

/-- First derivative of the normalized Newtonian kernel, defined as zero at its singularity. -/
def kernelDerivative (i : Fin 3) (z : Vec3) : ℝ :=
  if z = 0 then 0 else
    (4 * Real.pi)⁻¹ * z i * q z ^ (-(3 : ℝ) / 2)

/-- The smooth cutoff used in the annular harmonic representation. -/
def eta (x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ) : Vec3 → ℝ :=
  mollifiedBallCutoff x₀ hρ

/-- The Newtonian kernel times one cutoff derivative. -/
def kernelCutoffDerivative (x x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ)
    (i : Fin 3) (y : Vec3) : ℝ :=
  newtonianKernel (x - y) * spatialDeriv (eta x₀ hρ) i y

private lemma spatialDeriv_eta_eq_zero_on_closed_inner (x₀ : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) {y : Vec3} (hy : y ∈ euclideanClosedBall x₀ (13 * ρ / 20))
    (i : Fin 3) : spatialDeriv (eta x₀ hρ) i y = 0 := by
  have hgrad := mollifiedBallCutoff_derivatives_vanish_outside_annulus x₀ hρ
    (hx := fun h => h.2 hy)
  change (fderiv ℝ (eta x₀ hρ) y) (basisVec i) = 0
  have hi := congrFun hgrad.1 i
  simpa [eta, classicalGradient, classicalGradient_apply, CKN.basisVec_apply] using hi

lemma contDiff_spatialDeriv_two {f : Vec3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (i : Fin 3) :
    ContDiff ℝ (2 : ℕ) (spatialDeriv f i) := by
  have hfd := hf.contDiff_fderiv_apply (m := (2 : ℕ))
    (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)
  have hc : ContDiff ℝ (2 : ℕ)
      (fun x : Vec3 => (x, basisVec i)) := by
    fun_prop
  have hcomp := hfd.comp hc
  change ContDiff ℝ (2 : ℕ)
    (fun x : Vec3 => (fderiv ℝ f x) (basisVec i))
  exact hcomp

lemma spatialDeriv_eta_eventually_zero (x x₀ : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (hx : x ∈ euclideanBall x₀ (13 * ρ / 20)) (i : Fin 3) :
    ∀ᶠ y in 𝓝 x, spatialDeriv (eta x₀ hρ) i y = 0 := by
  have hopen : IsOpen (euclideanBall x₀ (13 * ρ / 20)) := by
    change IsOpen {y : Vec3 | euclideanSqDist y x₀ < (13 * ρ / 20) ^ 2}
    exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const
  obtain ⟨δ, hδ, hball⟩ := (Metric.isOpen_iff.mp hopen) x hx
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  apply spatialDeriv_eta_eq_zero_on_closed_inner x₀ hρ _ i
  apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
    (x₀ := x₀) (x := y) (by positivity)).2
  exact le_of_lt ((mem_euclideanBall_iff_vecEuclideanNorm_lt
    (x₀ := x₀) (x := y) (by positivity)).1 (hball hy))

private lemma kernelCutoffDerivative_contDiffAt (x x₀ : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (hx : x ∈ euclideanBall x₀ (13 * ρ / 20)) (i : Fin 3) (y : Vec3) :
    ContDiffAt ℝ (1 : ℕ) (kernelCutoffDerivative x x₀ hρ i) y := by
  by_cases hxy : x - y = 0
  · have heq : (kernelCutoffDerivative x x₀ hρ i) =ᶠ[𝓝 y]
        (fun _ : Vec3 => (0 : ℝ)) := by
      have hxy' : x = y := sub_eq_zero.mp hxy
      subst y
      filter_upwards [spatialDeriv_eta_eventually_zero x x₀ hρ hx i] with z hz
      simp [kernelCutoffDerivative, hz]
    have hzero : ContDiffAt ℝ (1 : ℕ) (fun _ : Vec3 => (0 : ℝ)) y :=
      (contDiff_const : ContDiff ℝ (1 : ℕ) (fun _ : Vec3 => (0 : ℝ))).contDiffAt
    exact hzero.congr_of_eventuallyEq heq
  · have hsub : ContDiffAt ℝ (2 : ℕ) (fun z : Vec3 => x - z) y := by
      fun_prop
    have hkernel : ContDiffAt ℝ (2 : ℕ)
        (fun z : Vec3 => newtonianKernel (x - z)) y := by
      simpa only [Function.comp_def] using
        (contDiffAt_newtonianKernel hxy).comp y hsub
    have heta0 : ContDiff ℝ (↑(⊤ : ℕ∞)) (eta x₀ hρ) := by
      simpa only [eta] using mollifiedBallCutoff_smooth x₀ hρ
    have heta : ContDiffAt ℝ (2 : ℕ)
        (spatialDeriv (eta x₀ hρ) i) y :=
      (contDiff_spatialDeriv_two heta0 i).contDiffAt
    have hprod := hkernel.mul heta
    change ContDiffAt ℝ (1 : ℕ)
      (fun z : Vec3 => newtonianKernel (x - z) *
        spatialDeriv (eta x₀ hρ) i z) y
    exact hprod.of_le (by norm_num)

lemma kernelCutoffDerivative_contDiff (x x₀ : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (hx : x ∈ euclideanBall x₀ (13 * ρ / 20)) (i : Fin 3) :
    ContDiff ℝ (1 : ℕ) (kernelCutoffDerivative x x₀ hρ i) :=
  contDiff_iff_contDiffAt.mpr (kernelCutoffDerivative_contDiffAt x x₀ hρ hx i)

lemma kernelCutoffDerivative_hasCompactSupport (x x₀ : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (i : Fin 3) :
    HasCompactSupport (kernelCutoffDerivative x x₀ hρ i) := by
  have hd : HasCompactSupport (spatialDeriv (eta x₀ hρ) i) :=
    (mollifiedBallCutoff_hasCompactSupport x₀ hρ).fderiv_apply
      (𝕜 := ℝ) (basisVec i)
  change HasCompactSupport (fun y : Vec3 => newtonianKernel (x - y) *
    spatialDeriv (eta x₀ hρ) i y)
  exact hd.mul_left

lemma kernelCutoffDerivative_integrable_mul_left {h : Vec3 → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (x x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (13 * ρ / 20)) (i : Fin 3) :
    Integrable (fun y : Vec3 =>
      spatialDeriv h i y * kernelCutoffDerivative x x₀ hρ i y) volume := by
  have hk : HasCompactSupport (kernelCutoffDerivative x x₀ hρ i) :=
    kernelCutoffDerivative_hasCompactSupport x x₀ hρ i
  have hkc : Continuous (kernelCutoffDerivative x x₀ hρ i) :=
    (kernelCutoffDerivative_contDiff x x₀ hρ hx i).continuous
  have hhc : Continuous (spatialDeriv h i) := by
    exact (hh.continuous_fderiv (by simp)).clm_apply continuous_const
  exact (hhc.mul hkc).integrable_of_hasCompactSupport hk.mul_left

lemma kernelCutoffDerivative_integrable_mul_right {h : Vec3 → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (x x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (13 * ρ / 20)) (i : Fin 3) :
    Integrable (fun y : Vec3 =>
      h y * CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y) volume := by
  have hk : HasCompactSupport (kernelCutoffDerivative x x₀ hρ i) :=
    kernelCutoffDerivative_hasCompactSupport x x₀ hρ i
  have hkc : ContDiff ℝ (1 : ℕ) (kernelCutoffDerivative x x₀ hρ i) :=
    kernelCutoffDerivative_contDiff x x₀ hρ hx i
  have hkd : Continuous (CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i) := by
    exact (hkc.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hhc : Continuous h := hh.continuous
  have hkdSupport : HasCompactSupport
      (CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i) :=
    hk.fderiv_apply (𝕜 := ℝ) (basisVec i)
  exact (hhc.mul hkd).integrable_of_hasCompactSupport hkdSupport.mul_left

private lemma kernelCutoffDerivative_integrable_mul_h {h : Vec3 → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (x x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (13 * ρ / 20)) (i : Fin 3) :
    Integrable (fun y : Vec3 =>
      h y * kernelCutoffDerivative x x₀ hρ i y) volume := by
  have hk : HasCompactSupport (kernelCutoffDerivative x x₀ hρ i) :=
    kernelCutoffDerivative_hasCompactSupport x x₀ hρ i
  have hkc : Continuous (kernelCutoffDerivative x x₀ hρ i) :=
    (kernelCutoffDerivative_contDiff x x₀ hρ hx i).continuous
  exact (hh.continuous.mul hkc).integrable_of_hasCompactSupport hk.mul_left

lemma integral_h_mul_kernelCutoffDerivative_spatialDeriv {h : Vec3 → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (x x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (13 * ρ / 20)) (i : Fin 3) :
    ∫ y : Vec3, h y * CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y =
      -∫ y : Vec3, spatialDeriv h i y * kernelCutoffDerivative x x₀ hρ i y := by
  have hleft := kernelCutoffDerivative_integrable_mul_left hh x x₀ hρ hx i
  have hright := kernelCutoffDerivative_integrable_mul_right hh x x₀ hρ hx i
  have hprod := kernelCutoffDerivative_integrable_mul_h hh x x₀ hρ hx i
  have hfdiff : ∀ y ∈ tsupport (kernelCutoffDerivative x x₀ hρ i),
      DifferentiableAt ℝ h y := by
    intro y hy
    exact hh.differentiable (by simp) y
  have hgdiff : ∀ y ∈ tsupport h,
      DifferentiableAt ℝ (kernelCutoffDerivative x x₀ hρ i) y := by
    intro y hy
    exact (kernelCutoffDerivative_contDiff x x₀ hρ hx i).differentiable
      (by norm_num) y
  simpa only [spatialDeriv] using
    (integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := volume) (v := basisVec i) hleft hright hprod hfdiff hgdiff)

lemma newtonianKernel_mul_compact_integrable {f : Vec3 → ℝ}
    (hf : Continuous f) (hfSupport : HasCompactSupport f) (x : Vec3) :
    Integrable (fun y : Vec3 => newtonianKernel (x - y) * f y) volume := by
  exact (locallyIntegrable_newtonianKernel_sub x).integrable_smul_right_of_hasCompactSupport
    hf hfSupport

theorem newtonianKernel_mul_compact_integrable_global {f : Vec3 → ℝ}
    (hf : Continuous f) (hfSupport : HasCompactSupport f) (x : Vec3) :
    Integrable (fun y : Vec3 => newtonianKernel (x - y) * f y) volume :=
  newtonianKernel_mul_compact_integrable hf hfSupport x

theorem newtonianKernel_size_bound {z : Vec3} (hz : z ≠ 0) :
    |newtonianKernel z| ≤ (4 * Real.pi)⁻¹ * ‖z‖⁻¹ := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hrn : 0 < vec3EuclideanNorm z :=
    lt_of_lt_of_le hzn (CKN.space_norm_le_euclideanNorm z)
  have hinv : (vec3EuclideanNorm z)⁻¹ ≤ ‖z‖⁻¹ := by
    exact (inv_le_inv₀ hrn hzn).2 (CKN.space_norm_le_euclideanNorm z)
  rw [newtonianKernel, abs_of_nonneg (by positivity)]
  rw [show 1 / (4 * Real.pi * vec3EuclideanNorm z) =
      (4 * Real.pi)⁻¹ * (vec3EuclideanNorm z)⁻¹ by field_simp]
  exact mul_le_mul_of_nonneg_left hinv (by positivity)

theorem newtonianKernel_continuousAt {z : Vec3} (hz : z ≠ 0) :
    ContinuousAt newtonianKernel z :=
  (contDiffAt_newtonianKernel hz).continuousAt

theorem newtonianKernel_hasFDerivAt {z : Vec3} (hz : z ≠ 0) :
    HasFDerivAt newtonianKernel (fderiv ℝ newtonianKernel z) z :=
  (contDiffAt_newtonianKernel hz).differentiableAt (by norm_num) |>.hasFDerivAt

theorem newtonianKernel_spatialDeriv_continuousAt {z : Vec3} (hz : z ≠ 0)
    (i : Fin 3) : ContinuousAt (CKN.spatialDeriv newtonianKernel i) z := by
  have hfd := (contDiffAt_newtonianKernel hz).continuousAt_fderiv (by norm_num)
  change ContinuousAt (fun w : Vec3 => (fderiv ℝ newtonianKernel w)
    (CKN.basisVec i)) z
  exact hfd.clm_apply continuousAt_const

theorem newtonianKernel_spatialDeriv_second_continuousAt
    {z : Vec3} (hz : z ≠ 0) (i j : Fin 3) :
    ContinuousAt (CKN.spatialDeriv (CKN.spatialDeriv newtonianKernel i) j) z := by
  have hfd : ContDiffAt ℝ (1 : ℕ)
      (fderiv ℝ newtonianKernel) z :=
    (contDiffAt_newtonianKernel hz).fderiv_right (m := (1 : ℕ))
      (by norm_num)
  have hi : ContDiffAt ℝ (1 : ℕ)
      (CKN.spatialDeriv newtonianKernel i) z := by
    change ContDiffAt ℝ (1 : ℕ)
      (fun w : Vec3 => (fderiv ℝ newtonianKernel w)
        (CKN.basisVec i)) z
    exact hfd.clm_apply contDiffAt_const
  have hj := hi.continuousAt_fderiv (by norm_num)
  change ContinuousAt (fun w : Vec3 =>
    (fderiv ℝ (CKN.spatialDeriv newtonianKernel i) w)
      (CKN.basisVec j)) z
  exact hj.clm_apply continuousAt_const

end CKN.Foundation.Heat
