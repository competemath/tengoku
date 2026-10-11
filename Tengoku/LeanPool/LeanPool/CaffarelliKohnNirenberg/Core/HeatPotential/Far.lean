/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.MorreySources
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.Campanato
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.GradientNorm
public import Tengoku

/-!
# Far

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric
open Filter

noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

theorem measurable_heatPotentialKernel_translate (w : ParabolicPoint) :
    Measurable (fun v : ParabolicPoint => heatPotentialKernel w v) := by
  rw [show (fun v : ParabolicPoint => heatPotentialKernel w v) =
      (fun v => heatKernel (w.1 - v.1) (w.2 - v.2)) by
      funext v
      unfold heatPotentialKernel pointSub
      exact heatKernelPlus_eq_heatKernel _]
  unfold heatKernel
  apply Measurable.ite
  · measurability
  · measurability
  · exact measurable_const

theorem vec3_norm_le_euclidean_norm (x : Vec3) :
    ‖x‖ ≤ vec3EuclideanNorm x := by
  rw [pi_norm_le_iff_of_nonneg (vec3EuclideanNorm_nonneg _)]
  intro i
  change |x i| ≤ vec3EuclideanNorm x
  unfold vec3EuclideanNorm
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum
    (fun j _hj => sq_nonneg (x j)) (Finset.mem_univ i)
theorem vec3EuclideanNorm_add_le (x y : Vec3) :
    vec3EuclideanNorm (x + y) ≤ vec3EuclideanNorm x + vec3EuclideanNorm y := by
  rw [vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2]
  simpa only [WithLp.toLp_add] using norm_add_le (WithLp.toLp 2 x) (WithLp.toLp 2 y)
theorem parabolic_ball_segment_mem
    {z p p' y : ParabolicPoint} {r : ℝ}
    (hp : p ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
    (hp' : p' ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
    (hy : y.1 ∈ segment ℝ p.1 p'.1) (hytime : y.2 = p.2) :
    y ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r := by
  rw [Metric.mem_closedBall, dist_eq_parabolicDist] at hp hp' ⊢
  have hps : vec3EuclideanNorm (p.1 - z.1) ≤ r :=
    (le_max_left _ _).trans hp
  have hps' : vec3EuclideanNorm (p'.1 - z.1) ≤ r :=
    (le_max_left _ _).trans hp'
  have hpt : Real.sqrt |p.2 - z.2| ≤ r := (le_max_right _ _).trans hp
  have hyt : Real.sqrt |y.2 - z.2| ≤ r := by simpa [hytime] using hpt
  rcases hy with ⟨a, b, ha, hb, hab, hy⟩
  have hspace : vec3EuclideanNorm (y.1 - z.1) ≤ r := by
    rw [← hy]
    have heq : a • p.1 + b • p'.1 - z.1 =
        a • (p.1 - z.1) + b • (p'.1 - z.1) := by
      rw [smul_sub, smul_sub]
      have hz : -(z.1) = (a + b) • (-(z.1)) := by
        rw [hab, one_smul]
      rw [sub_eq_add_neg, hz]
      module
    rw [heq]
    calc
      vec3EuclideanNorm (a • (p.1 - z.1) + b • (p'.1 - z.1)) ≤
          vec3EuclideanNorm (a • (p.1 - z.1)) +
            vec3EuclideanNorm (b • (p'.1 - z.1)) :=
        vec3EuclideanNorm_add_le _ _
      _ = a * vec3EuclideanNorm (p.1 - z.1) +
            b * vec3EuclideanNorm (p'.1 - z.1) := by
        rw [vec3EuclideanNorm_smul, vec3EuclideanNorm_smul,
          abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * r + b * r := add_le_add
        (mul_le_mul_of_nonneg_left hps ha)
        (mul_le_mul_of_nonneg_left hps' hb)
      _ = r := by rw [← add_mul, hab, one_mul]
  exact max_le hspace hyt
theorem parabolic_ball_time_segment_mem
    {z p p' : ParabolicPoint} {x : Vec3} {r s : ℝ}
    (hr : 0 ≤ r)
    (hp : p ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
    (hp' : p' ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
    (hx : vec3EuclideanNorm (x - z.1) ≤ r)
    (hs : s ∈ Set.Icc p.2 p'.2) :
    (let q : ParabolicPoint := (x, s); q) ∈
      @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r := by
  rw [Metric.mem_closedBall, dist_eq_parabolicDist] at hp hp'
  change dist (let q : ParabolicPoint := (x, s); q) z ≤ r
  rw [dist_eq_parabolicDist]
  have htp : Real.sqrt |p.2 - z.2| ≤ r := (le_max_right _ _).trans hp
  have htp' : Real.sqrt |p'.2 - z.2| ≤ r := (le_max_right _ _).trans hp'
  have habsp : |p.2 - z.2| ≤ r ^ 2 := by
    have hsq := Real.sq_sqrt (abs_nonneg (p.2 - z.2))
    nlinarith only [hsq, htp, hr, Real.sqrt_nonneg (|p.2 - z.2|)]
  have habsp' : |p'.2 - z.2| ≤ r ^ 2 := by
    have hsq := Real.sq_sqrt (abs_nonneg (p'.2 - z.2))
    nlinarith only [hsq, htp', hr, Real.sqrt_nonneg (|p'.2 - z.2|)]
  have hlow : -(r ^ 2) ≤ s - z.2 := by
    have hlowp : -(r ^ 2) ≤ p.2 - z.2 := (abs_le.mp habsp).1
    linarith only [hlowp, hs.1]
  have hhigh : s - z.2 ≤ r ^ 2 := by
    have hhighp : p'.2 - z.2 ≤ r ^ 2 := (abs_le.mp habsp').2
    linarith only [hhighp, hs.2]
  apply max_le hx
  rw [Real.sqrt_le_iff]
  exact ⟨hr, (abs_le.mpr ⟨hlow, hhigh⟩).trans_eq rfl⟩
/-! The source shells used by the far part start six dyadic scales outside the
    observation ball.  The larger gap makes the causal kernel separation
    uniform after moving the observation point inside its ball. -/
end CKN.Core.HeatPotential
