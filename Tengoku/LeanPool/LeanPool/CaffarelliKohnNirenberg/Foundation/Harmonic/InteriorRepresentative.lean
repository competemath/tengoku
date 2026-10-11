/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorWeak
public import Tengoku

/-!
# Interior Representative

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology Convolution
open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Foundation.Heat

/-! The fixed-annulus representative used for weakly harmonic functions. -/

/-- Interior representative constructed from a weakly harmonic function by Newtonian integration.
-/
noncomputable def weakHarmonicInteriorRepresentative
    (h : Vec3 → ℝ) (x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ) (x : Vec3) : ℝ :=
  (-∫ y : Vec3, newtonianKernel (x - y) *
      (h y * CKN.spatialLaplacian (eta x₀ hρ) y)) +
    2 * ∑ i : Fin 3, ∫ y : Vec3,
      h y * CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y

/-- Source coefficient in the weakly harmonic interior representation estimate. -/
noncomputable def weakHarmonicInteriorSourceConstant : ℝ :=
  (4 * Real.pi)⁻¹ * 60 * cutoffSecondDerivativeConstant

/-- Cutoff-derivative coefficient in the weakly harmonic representation estimate. -/
noncomputable def weakHarmonicInteriorCutoffConstant : ℝ :=
  (4 * Real.pi)⁻¹ * (400 * cutoffGradientConstant +
    20 * cutoffSecondDerivativeConstant)

/-- Spatial-gradient coefficient for the cutoff part of the weak harmonic representation. -/
noncomputable def weakHarmonicInteriorXGradientConstant : ℝ :=
  (4 * Real.pi)⁻¹ * (32000 * cutoffGradientConstant +
    400 * cutoffSecondDerivativeConstant)

/-- Spatial-gradient coefficient for the source part of the weak harmonic representation. -/
noncomputable def weakHarmonicInteriorSourceXGradientConstant : ℝ :=
  (4 * Real.pi)⁻¹ * (1200 * cutoffSecondDerivativeConstant)

/-- Supremum coefficient for the weakly harmonic interior representative. -/
noncomputable def weakHarmonicInteriorSupConstant : ℝ :=
  (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) *
    (weakHarmonicInteriorSourceConstant +
      6 * weakHarmonicInteriorCutoffConstant)

/-- Gradient coefficient for the weakly harmonic interior representative. -/
noncomputable def weakHarmonicInteriorGradientConstant : ℝ :=
  (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) *
    (weakHarmonicInteriorSourceConstant +
      6 * weakHarmonicInteriorXGradientConstant)

lemma weakHarmonicInteriorSourceConstant_nonneg :
    0 ≤ weakHarmonicInteriorSourceConstant := by
  dsimp [weakHarmonicInteriorSourceConstant]
  have hS := cutoffSecondDerivativeConstant_nonneg_global
  positivity

lemma weakHarmonicInteriorCutoffConstant_nonneg :
    0 ≤ weakHarmonicInteriorCutoffConstant := by
  dsimp [weakHarmonicInteriorCutoffConstant]
  have hG := cutoffGradientConstant_nonneg_global
  have hS := cutoffSecondDerivativeConstant_nonneg_global
  positivity

lemma weakHarmonicInteriorXGradientConstant_nonneg :
    0 ≤ weakHarmonicInteriorXGradientConstant := by
  dsimp [weakHarmonicInteriorXGradientConstant]
  have hG := cutoffGradientConstant_nonneg_global
  have hS := cutoffSecondDerivativeConstant_nonneg_global
  positivity

lemma weakHarmonicInteriorSupConstant_nonneg :
    0 ≤ weakHarmonicInteriorSupConstant := by
  dsimp [weakHarmonicInteriorSupConstant]
  have hS := weakHarmonicInteriorSourceConstant_nonneg
  have hC := weakHarmonicInteriorCutoffConstant_nonneg
  positivity

lemma weakHarmonicInteriorSourceXGradientConstant_nonneg :
    0 ≤ weakHarmonicInteriorSourceXGradientConstant := by
  dsimp [weakHarmonicInteriorSourceXGradientConstant]
  have hS := cutoffSecondDerivativeConstant_nonneg_global
  positivity

lemma weak_annulus_distance
    {x x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (ρ / 2))
    {y : Vec3} (hy : y ∈ cutoffAnnulus x₀ ρ) :
    ρ / 20 < ‖x - y‖ := by
  have hx' : vec3EuclideanNorm (x - x₀) < ρ / 2 :=
    by
      simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
        (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hx
  have hy' : 13 * ρ / 20 < vec3EuclideanNorm (y - x₀) := by
    have hnot : y ∉ euclideanClosedBall x₀ (13 * ρ / 20) := hy.2
    by_contra hle
    apply hnot
    apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
    exact le_of_not_gt (by
      simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using hle)
  have htri : vec3EuclideanNorm (y - x₀) ≤
      vec3EuclideanNorm (x - y) + vec3EuclideanNorm (x - x₀) := by
    rw [vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2,
      vec3EuclideanNorm_eq_l2]
    calc
      ‖WithLp.toLp 2 (y - x₀)‖ =
          ‖WithLp.toLp 2 ((y - x) + (x - x₀))‖ := by
            congr 1
            ext i
            simp only [Pi.add_apply, Pi.sub_apply]
            ring
      _ ≤ ‖WithLp.toLp 2 (y - x)‖ +
          ‖WithLp.toLp 2 (x - x₀)‖ := norm_add_le _ _
      _ = ‖WithLp.toLp 2 (x - y)‖ +
          ‖WithLp.toLp 2 (x - x₀)‖ := by
            have hneg : y - x = -(x - y) := by
              ext i
              simp only [Pi.neg_apply, Pi.sub_apply]
              ring
            rw [hneg, WithLp.toLp_neg, norm_neg]
  have hvec : 3 * (ρ / 20) < vec3EuclideanNorm (x - y) := by
    nlinarith only [hy', htri, hx', hρ]
  have hthree := CKN.euclideanNorm_le_three_mul_space_norm (x - y)
  have hthree' : vec3EuclideanNorm (x - y) ≤ 3 * ‖x - y‖ := by
    simpa only [CKN.spaceEuclideanNorm, vec3EuclideanNorm] using hthree
  nlinarith only [hvec, hthree', hρ]

lemma weak_annulus_subset_outer
    {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) :
    cutoffAnnulus x₀ ρ ⊆ euclideanBall x₀ ρ := by
  intro y hy
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).2
  have hy' := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hy.1
  have hy'' : vecEuclideanNorm (y - x₀) < ρ := by
    exact hy'.trans (by
      calc
        3 * ρ / 4 = (3 / 4 : ℝ) * ρ := by ring
        _ < 1 * ρ := by gcongr; norm_num
        _ = ρ := by ring)
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using hy''

lemma weak_source_kernel_bound
    {x x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (ρ / 2))
    {y : Vec3} (hy : y ∈ cutoffAnnulus x₀ ρ) :
    |newtonianKernel (x - y) *
        CKN.spatialLaplacian (eta x₀ hρ) y| ≤
      weakHarmonicInteriorSourceConstant * (ρ ^ 3)⁻¹ := by
  have hd := weak_annulus_distance hρ hx hy
  have hxy : x - y ≠ 0 := by
    intro hzero
    rw [hzero] at hd
    exact (not_lt_of_ge (by positivity : 0 ≤ ρ / 20)) (by simpa using hd)
  have hk := newtonianKernel_size_bound hxy
  have hki : ‖x - y‖⁻¹ ≤ (ρ / 20)⁻¹ := by
    exact (inv_le_inv₀ (by positivity) (by positivity)).2 hd.le
  have hs := eta_laplacian_bound_global x₀ hρ y
  rw [abs_mul]
  calc
    |newtonianKernel (x - y)| *
        |CKN.spatialLaplacian (eta x₀ hρ) y| ≤
      ((4 * Real.pi)⁻¹ * (ρ / 20)⁻¹) *
        (3 * cutoffSecondDerivativeConstant / ρ ^ 2) := by
          gcongr
          exact hk.trans (mul_le_mul_of_nonneg_left hki (by positivity))
    _ = weakHarmonicInteriorSourceConstant * (ρ ^ 3)⁻¹ := by
      dsimp [weakHarmonicInteriorSourceConstant]
      field_simp [hρ.ne']
      ring

lemma weak_source_kernel_zero_off_annulus
    {x x₀ y : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hy : y ∉ cutoffAnnulus x₀ ρ) :
    newtonianKernel (x - y) *
        CKN.spatialLaplacian (eta x₀ hρ) y = 0 := by
  rw [eta_laplacian_zero_off_annulus hρ hy, mul_zero]

lemma weak_annulus_isFinite
    {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) :
    volume (cutoffAnnulus x₀ ρ) ≠ ∞ := by
  apply ne_of_lt
  have hclosed : cutoffAnnulus x₀ ρ ⊆ euclideanClosedBall x₀ ρ := by
    intro y hy
    apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hρ.le).2
    exact ((mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).1
      (weak_annulus_subset_outer hρ hy)).le
  exact lt_of_le_of_lt (measure_mono hclosed)
    ((isCompact_euclideanClosedBall x₀ hρ.le).measure_lt_top)

lemma weak_source_kernel_continuousOn
    {x x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (ρ / 2)) :
    ContinuousOn (fun y : Vec3 => newtonianKernel (x - y) *
      CKN.spatialLaplacian (eta x₀ hρ) y) (cutoffAnnulus x₀ ρ) := by
  intro y hy
  have hd := weak_annulus_distance hρ hx hy
  have hxy : x - y ≠ 0 := by
    intro hzero
    rw [hzero] at hd
    exact (not_lt_of_ge (by positivity : 0 ≤ ρ / 20)) (by simpa using hd)
  have hN : ContinuousAt (fun z : Vec3 => newtonianKernel (x - z)) y :=
    (newtonianKernel_continuousAt hxy).comp
      (continuousAt_const.sub continuousAt_id)
  have hD : Continuous (CKN.spatialLaplacian (eta x₀ hρ)) := by
    simpa only [eta] using
      (CKN.contDiff_spatialLaplacian_smooth
        (mollifiedBallCutoff_smooth x₀ hρ)).continuous
  exact hN.continuousWithinAt.mul hD.continuousAt.continuousWithinAt

lemma weak_cutoff_kernel_continuousOn
    {x x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (ρ / 2)) (i : Fin 3) :
    ContinuousOn (fun y : Vec3 =>
      CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y)
      (cutoffAnnulus x₀ ρ) := by
  have hxinner : x ∈ euclideanBall x₀ (13 * ρ / 20) := by
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2
    have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hx
    exact hx'.trans (by nlinarith only [hρ])
  have hcont : Continuous (fun y : Vec3 =>
      CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y) := by
    exact ((kernelCutoffDerivative_contDiff_one x x₀ hρ hxinner i).continuous_fderiv
      (by norm_num)).clm_apply continuous_const
  exact hcont.continuousOn

end CKN.Foundation.Heat
