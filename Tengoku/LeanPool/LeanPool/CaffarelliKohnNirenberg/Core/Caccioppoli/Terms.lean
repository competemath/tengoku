/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.Cutoff
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.Derivatives

/-!
# Terms

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN

theorem caccioppoli_heat_cutoff_eq_one_on
    (x₀ : Vec3) (t₀ ρ ε r : ℝ) (hρ : 0 < ρ) (hε : 0 < ε)
    (hr : 0 < r) (hscale : r ≤ ρ / 2)
    {z : Vec3 × ℝ}
    (hx : z.1 ∈ vec3Ball x₀ (ρ / 2))
    (ht : z.2 ∈ Ioc (t₀ - r ^ 2) (t₀ + ε / 2)) :
    caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε z = 1 := by
  unfold caccioppoliHeatCutoff
  rw [mollifiedBallCutoff_eq_one_on_inner x₀ hρ]
  · rw [caccioppoli_asymmetricTimeCutoff_eq_one_on hρ hε hr hscale
      ⟨ht.1.le, ht.2.trans (by linarith only [hε])⟩]
    norm_num
  · apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2
    have hrad : ρ / 2 ≤ 13 * ρ / 20 := by linarith only [hρ]
    have hx' : CKN.vecEuclideanNorm (z.1 - x₀) < ρ / 2 := by
      have hnorm : ∀ v : Vec3, vec3EuclideanNorm v = CKN.vecEuclideanNorm v := by
        intro v
        simp [vec3EuclideanNorm, CKN.vecEuclideanNorm, vecNormSq, vecDot, pow_two]
      rw [← hnorm]
      exact mem_vec3Ball.mp hx
    exact (hx'.trans_le hrad)

private theorem caccioppoli_heat_cutoff_eq_one_near
    (x₀ : Vec3) (t₀ ρ ε r : ℝ) (hρ : 0 < ρ) (hε : 0 < ε)
    (hr : 0 < r) (hscale : r ≤ ρ / 2) {z : Vec3 × ℝ}
    (hx : z.1 ∈ vec3Ball x₀ (ρ / 2))
    (ht : z.2 ∈ Ioc (t₀ - r ^ 2) t₀) :
    ∀ᶠ y in 𝓝 z,
      caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε y = 1 := by
  have hopen : IsOpen (vec3Ball x₀ (ρ / 2)) := by
    have hnorm : Continuous (vec3EuclideanNorm : Vec3 → ℝ) := by
      unfold vec3EuclideanNorm
      fun_prop
    exact isOpen_lt (hnorm.comp (continuous_id.sub continuous_const)) continuous_const
  have hspace : ∀ᶠ y in 𝓝 z, y.1 ∈ vec3Ball x₀ (ρ / 2) := by
    have hset : vec3Ball x₀ (ρ / 2) ∈ 𝓝 z.1 := hopen.mem_nhds hx
    exact continuous_fst.continuousAt.preimage_mem_nhds hset
  have htime : ∀ᶠ y in 𝓝 z,
      y.2 ∈ Ioo (t₀ - r ^ 2) (t₀ + ε / 2) := by
    apply continuous_snd.continuousAt.preimage_mem_nhds
    apply isOpen_Ioo.mem_nhds
    constructor
    · exact ht.1
    · linarith only [ht.2, hε]
  filter_upwards [hspace, htime] with y hyx hyt
  exact caccioppoli_heat_cutoff_eq_one_on x₀ t₀ ρ ε r hρ hε hr hscale
    hyx ⟨hyt.1, hyt.2.le⟩

theorem caccioppoli_heat_cutoff_derivatives_zero_on_inner
    (x₀ : Vec3) (t₀ ρ ε r : ℝ) (hρ : 0 < ρ) (hε : 0 < ε)
    (hr : 0 < r) (hscale : r ≤ ρ / 2) {z : ParabolicPoint}
    (hx : z.1 ∈ vec3Ball x₀ (ρ / 2))
    (ht : z.2 ∈ Ioc (t₀ - r ^ 2) t₀) :
    timePartial (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) z = 0 ∧
      (∀ i : Fin 3,
        spatialPartial (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) i z = 0) ∧
      (∀ i j : Fin 3,
        spatialSecondPartial (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) i j z = 0) := by
  have hev := caccioppoli_heat_cutoff_eq_one_near x₀ t₀ ρ ε r hρ hε hr hscale hx ht
  have hev_time : (fun s : ℝ =>
      caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε (z.1, s)) =ᶠ[𝓝 z.2]
        (fun _ => (1 : ℝ)) := by
    have hmap : Continuous (fun s : ℝ => (z.1, s)) :=
      continuous_const.prodMk continuous_id
    filter_upwards [hmap.continuousAt.preimage_mem_nhds hev] with s hs
    exact hs
  have htime : timePartial (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) z = 0 := by
    unfold timePartial
    rw [hev_time.fderiv_eq, fderiv_const_apply]
    simp
  have hspace (i : Fin 3) :
      spatialPartial (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) i z = 0 := by
    unfold spatialPartial
    have hmap : Continuous (fun x : Vec3 => (x, z.2)) :=
      continuous_id.prodMk continuous_const
    have hev_space : (fun x : Vec3 =>
        caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε (x, z.2)) =ᶠ[𝓝 z.1]
          (fun _ => (1 : ℝ)) := by
      filter_upwards [hmap.continuousAt.preimage_mem_nhds hev] with x hx'
      exact hx'
    rw [hev_space.fderiv_eq, fderiv_const_apply]
    simp
  have hsecond (i j : Fin 3) :
      spatialSecondPartial (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) i j z = 0 := by
    unfold spatialSecondPartial
    change (fderiv ℝ (fun x : Vec3 =>
      spatialPartial (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) i (x, z.2))
      z.1) (basisVec j) = 0
    have hopen : IsOpen (vec3Ball x₀ (ρ / 2)) := by
      have hnorm : Continuous (vec3EuclideanNorm : Vec3 → ℝ) := by
        unfold vec3EuclideanNorm
        fun_prop
      exact isOpen_lt (hnorm.comp (continuous_id.sub continuous_const)) continuous_const
    have hinner : ∀ᶠ x in 𝓝 z.1, x ∈ vec3Ball x₀ (ρ / 2) := by
      have hset : vec3Ball x₀ (ρ / 2) ∈ 𝓝 z.1 := hopen.mem_nhds hx
      exact continuous_id.continuousAt.preimage_mem_nhds hset
    have hnear : (fun x : Vec3 =>
        spatialPartial (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) i (x, z.2)) =ᶠ[𝓝 z.1]
          (fun _ => (0 : ℝ)) := by
      filter_upwards [hinner] with x hxin
      unfold spatialPartial
      change (fderiv ℝ (fun y : Vec3 =>
        caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε (y, z.2)) x) (basisVec i) = 0
      have hlocal := caccioppoli_heat_cutoff_eq_one_near x₀ t₀ ρ ε r
        (z := (x, z.2)) hρ hε hr hscale hxin
        ⟨ht.1, ht.2.trans (by linarith only [hε])⟩
      have hmap : Continuous (fun y : Vec3 => (y, z.2)) :=
        continuous_id.prodMk continuous_const
      have hconst : (fun y : Vec3 =>
          caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε (y, z.2)) =ᶠ[𝓝 x]
            (fun _ => (1 : ℝ)) :=
        hmap.continuousAt.preimage_mem_nhds hlocal
      rw [hconst.fderiv_eq, fderiv_const_apply]
      simp
    rw [hnear.fderiv_eq, fderiv_const_apply]
    simp
  exact ⟨htime, hspace, hsecond⟩

theorem caccioppoli_cutoff_le_one
    {x₀ : Vec3} {t₀ ρ R : ℝ} (hρ : 0 < ρ) (hR : ρ / 2 < R)
    (z : Vec3 × ℝ) :
    caccioppoliCutoff x₀ t₀ ρ R hρ hR z ≤ 1 := by
  unfold caccioppoliCutoff
  calc
    mollifiedBallCutoff x₀ hρ z.1 * timeCutoff t₀ (ρ / 2) R z.2 ≤
        1 * timeCutoff t₀ (ρ / 2) R z.2 :=
      mul_le_mul_of_nonneg_right (mollifiedBallCutoff_le_one x₀ hρ z.1)
        (timeCutoff_nonneg t₀ (ρ / 2) R z.2)
    _ ≤ 1 * 1 :=
      mul_le_mul_of_nonneg_left
        (timeCutoff_le_one t₀ (ρ / 2) R z.2) (by positivity)
    _ = 1 := by ring

theorem caccioppoli_heat_function_upper_on_annulus
    {x₀ : Vec3} {t₀ ρ r : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hscale : r ≤ ρ / 2) {z : ParabolicPoint}
    (hp : (z.1 - x₀, z.2 - t₀) ∈
      parabolicCylinder 0 0 ρ \ parabolicCylinder 0 0 (ρ / 2)) :
    backwardHeatTestFunction r (z.1 - x₀) (z.2 - t₀) ≤
      8000000 * r ^ 2 / ρ ^ 3 := by
  simpa only [sub_zero] using
    (backwardHeatTestFunction_upper_on_annulus hr hρ hscale hp)

theorem caccioppoli_heat_spatial_derivative_abs_on_annulus
    {x₀ : Vec3} {t₀ ρ r : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hscale : r ≤ ρ / 2) {z : ParabolicPoint} (i : Fin 3)
    (hp : (z.1 - x₀, z.2 - t₀) ∈
      parabolicCylinder 0 0 ρ \ parabolicCylinder 0 0 (ρ / 2)) :
    |r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
        (r ^ 2 - (z.2 - t₀)) i| ≤
      5000000 * r ^ 2 / ρ ^ 4 := by
  have hgrad := backwardHeatTestGradient_upper_on_annulus hr hρ hscale hp
  have hcoord : |heatKernelSpaceDerivative (z.1 - x₀)
      (r ^ 2 - (z.2 - t₀)) i| ≤
      heatKernelGradientNorm (z.1 - x₀) (r ^ 2 - (z.2 - t₀)) := by
    unfold heatKernelGradientNorm
    exact Finset.single_le_sum (f := fun j =>
      |heatKernelSpaceDerivative (z.1 - x₀)
        (r ^ 2 - (z.2 - t₀)) j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
  rw [abs_mul]
  rw [abs_of_nonneg (sq_nonneg r)]
  calc
    r ^ 2 * |heatKernelSpaceDerivative (z.1 - x₀)
        (r ^ 2 - (z.2 - t₀)) i| ≤
        r ^ 2 * heatKernelGradientNorm (z.1 - x₀)
          (r ^ 2 - (z.2 - t₀)) := by
      gcongr
    _ = backwardHeatTestGradientNorm r (z.1 - x₀) (z.2 - t₀) := by
      rfl
    _ ≤ 5000000 * r ^ 2 / ρ ^ 4 := hgrad

end CKN
