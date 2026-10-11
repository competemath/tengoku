/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.FarShell

/-!
# Far Oscillation

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

theorem heatPotential_far_shell_two_step_oscillation
    {K : ParabolicPoint → ℝ} {z p p' v : ParabolicPoint} {r A B : ℝ}
    (hp : p ∈ @Metric.closedBall ParabolicPoint
      parabolicPseudoMetricSpace z r)
    (hp' : p' ∈ @Metric.closedBall ParabolicPoint
      parabolicPseudoMetricSpace z r)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hspace :
      |K (p.1 - v.1, p.2 - v.2) -
        K (p'.1 - v.1, p.2 - v.2)| ≤ A * vec3EuclideanNorm (p.1 - p'.1))
    (htime :
      |K (p'.1 - v.1, p.2 - v.2) -
        K (p'.1 - v.1, p'.2 - v.2)| ≤ B * |p.2 - p'.2|) :
    |K (p.1 - v.1, p.2 - v.2) -
        K (p'.1 - v.1, p'.2 - v.2)| ≤
      2 * r * (A + 2 * r * B) := by
  have hdist : parabolicDist p p' ≤ 2 * r := by
    rw [← dist_eq_parabolicDist]
    calc
      dist p p' ≤ dist p z + dist z p' := dist_triangle _ _ _
      _ ≤ r + r := add_le_add (by simpa [dist_comm] using hp)
        (by rw [dist_comm]; simpa using hp')
      _ = 2 * r := by ring
  have hspace_dist : vec3EuclideanNorm (p.1 - p'.1) ≤ 2 * r := by
    have hcomponent : vec3EuclideanNorm (p.1 - p'.1) ≤ parabolicDist p p' := by
      exact le_max_left _ _
    exact hcomponent.trans hdist
  have htime_dist : Real.sqrt |p.2 - p'.2| ≤ 2 * r := by
    have hcomponent : Real.sqrt |p.2 - p'.2| ≤ parabolicDist p p' := by
      exact le_max_right _ _
    exact hcomponent.trans hdist
  have habs_time : |p.2 - p'.2| ≤ (2 * r) ^ 2 := by
    have hsquare : (Real.sqrt |p.2 - p'.2|) ^ 2 = |p.2 - p'.2| :=
      Real.sq_sqrt (abs_nonneg _)
    have hsqrt_nonneg : 0 ≤ Real.sqrt |p.2 - p'.2| := Real.sqrt_nonneg _
    nlinarith only [hsquare, hsqrt_nonneg, htime_dist]
  calc
    |K (p.1 - v.1, p.2 - v.2) -
        K (p'.1 - v.1, p'.2 - v.2)| ≤
        |K (p.1 - v.1, p.2 - v.2) -
          K (p'.1 - v.1, p.2 - v.2)| +
        |K (p'.1 - v.1, p.2 - v.2) -
          K (p'.1 - v.1, p'.2 - v.2)| := by
      simpa only [sub_eq_add_neg, add_sub_assoc] using
        abs_sub_le _ _ _
    _ ≤ A * vec3EuclideanNorm (p.1 - p'.1) + B * |p.2 - p'.2| :=
      add_le_add hspace htime
    _ ≤ A * (2 * r) + B * (2 * r) ^ 2 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hspace_dist hA)
        (mul_le_mul_of_nonneg_left habs_time hB)
    _ = 2 * r * (A + 2 * r * B) := by ring

theorem heatPotential_far_shell_integral_oscillation_bound
    {F : ParabolicPoint → ℝ} {z p p' : ParabolicPoint} {r : ℝ}
    {j : ℕ} {C : ℝ} {M : ℝ≥0∞} (hr : 0 < r)
    (hF : AEMeasurable F volume)
    (hp : p ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
    (hp' : p' ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
    (hfinite : (∫⁻ v in heatPotentialFarShellSet z r j,
      ENNReal.ofReal |F v|) < ∞)
    (hMtop : M ≠ ∞)
    (hM : (∫⁻ v in heatPotentialFarShellSet z r j,
      ENNReal.ofReal |F v|) ≤ M)
    (hpoint : ∀ v ∈ heatPotentialFarShellSet z r j,
      |heatPotentialKernel p v - heatPotentialKernel p' v| ≤ C)
    (hC : 0 ≤ C) :
    |(∫ v in heatPotentialFarShellSet z r j,
        heatPotentialKernel p v * F v) -
      ∫ v in heatPotentialFarShellSet z r j,
        heatPotentialKernel p' v * F v| ≤ C * M.toReal := by
  let S : Set ParabolicPoint := heatPotentialFarShellSet z r j
  have hS : MeasurableSet S := measurableSet_heatPotentialFarShellSet z r j
  have hsource := integrableOn_abs_of_lintegral_lt_top hF hfinite
  have hK : ∀ q : ParabolicPoint,
      AEMeasurable (fun v : ParabolicPoint => heatPotentialKernel q v) volume := by
    intro q
    exact (measurable_heatPotentialKernel_translate q).aemeasurable
  let C₀ : ℝ := 1000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 3
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀]
    positivity
  have hKp : ∀ v ∈ S, |heatPotentialKernel p v| ≤ C₀ := by
    intro v hv
    exact heatPotential_far_shell_kernel_abs_le hr hp hv
  have hKp' : ∀ v ∈ S, |heatPotentialKernel p' v| ≤ C₀ := by
    intro v hv
    exact heatPotential_far_shell_kernel_abs_le hr hp' hv
  have hwi := integrableOn_mul_of_abs_integrable_of_bound hS hF (hK p)
    hfinite hC₀ hKp
  have hwi' := integrableOn_mul_of_abs_integrable_of_bound hS hF (hK p')
    hfinite hC₀ hKp'
  have hmajor : IntegrableOn (fun v => C * |F v|) S volume :=
    hsource.const_mul C
  have hsingle := heatPotential_single_kernel_shell_bound hC hS hwi hwi'
    hmajor hpoint
  have hsource' := real_integral_abs_le_of_lintegral_le hF hfinite hMtop hM
  exact hsingle.trans (mul_le_mul_of_nonneg_left hsource' hC)

theorem heatPotential_far_shell_spatial_integral_oscillation_bound
    {i : Fin 3} {G : ParabolicPoint → ℝ} {z p p' : ParabolicPoint} {r : ℝ}
    {j : ℕ} {C : ℝ} {M : ℝ≥0∞} (hr : 0 < r)
    (hG : AEMeasurable G volume)
    (hp : p ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
    (hp' : p' ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
    (hfinite : (∫⁻ v in heatPotentialFarShellSet z r j,
      ENNReal.ofReal |G v|) < ∞)
    (hMtop : M ≠ ∞)
    (hM : (∫⁻ v in heatPotentialFarShellSet z r j,
      ENNReal.ofReal |G v|) ≤ M)
    (hpoint : ∀ v ∈ heatPotentialFarShellSet z r j,
      |heatPotentialSpatialKernel i p v - heatPotentialSpatialKernel i p' v| ≤ C)
    (hC : 0 ≤ C) :
    |(∫ v in heatPotentialFarShellSet z r j,
        heatPotentialSpatialKernel i p v * G v) -
      ∫ v in heatPotentialFarShellSet z r j,
        heatPotentialSpatialKernel i p' v * G v| ≤ C * M.toReal := by
  let S : Set ParabolicPoint := heatPotentialFarShellSet z r j
  have hS : MeasurableSet S := measurableSet_heatPotentialFarShellSet z r j
  have hsource := integrableOn_abs_of_lintegral_lt_top hG hfinite
  have hK : ∀ q : ParabolicPoint,
      AEMeasurable (fun v : ParabolicPoint => heatPotentialSpatialKernel i q v) volume := by
    intro q
    exact (measurable_heatPotentialSpatialKernel_translate i q).aemeasurable
  let C₀ : ℝ := 300000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 4
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀]
    positivity
  have hKp : ∀ v ∈ S, |heatPotentialSpatialKernel i p v| ≤ C₀ := by
    intro v hv
    exact heatPotential_far_shell_spatial_kernel_abs_le hr hp hv
  have hKp' : ∀ v ∈ S, |heatPotentialSpatialKernel i p' v| ≤ C₀ := by
    intro v hv
    exact heatPotential_far_shell_spatial_kernel_abs_le hr hp' hv
  have hwi := integrableOn_mul_of_abs_integrable_of_bound hS hG (hK p)
    hfinite hC₀ hKp
  have hwi' := integrableOn_mul_of_abs_integrable_of_bound hS hG (hK p')
    hfinite hC₀ hKp'
  have hmajor : IntegrableOn (fun v => C * |G v|) S volume :=
    hsource.const_mul C
  have hsingle := heatPotential_single_kernel_shell_bound hC hS hwi hwi'
    hmajor hpoint
  have hsource' := real_integral_abs_le_of_lintegral_le hG hfinite hMtop hM
  exact hsingle.trans (mul_le_mul_of_nonneg_left hsource' hC)

theorem heatPotential_integral_near_far_split
    {f : ParabolicPoint → ℝ} {z : ParabolicPoint} {r : ℝ}
    (hcover : (Set.univ : Set ParabolicPoint) = heatPotentialNearSet z r ∪
      ⋃ j : ℕ, heatPotentialFarShellSet z r j)
    (hdST : ∀ j : ℕ, Disjoint (heatPotentialNearSet z r)
      (heatPotentialFarShellSet z r j))
    (hdT : Pairwise (Function.onFun Disjoint (heatPotentialFarShellSet z r)))
    (hInt : IntegrableOn f (heatPotentialNearSet z r ∪
      ⋃ j : ℕ, heatPotentialFarShellSet z r j) volume) :
    ∫ v, f v = (∫ v in heatPotentialNearSet z r, f v) +
      ∑' j : ℕ, ∫ v in heatPotentialFarShellSet z r j, f v := by
  have huniv : (∫ v, f v) = ∫ v in (Set.univ : Set ParabolicPoint), f v := by
    rw [Measure.restrict_univ]
  rw [huniv, hcover]
  have hT : ∀ j : ℕ, MeasurableSet (heatPotentialFarShellSet z r j) :=
    fun j => measurableSet_heatPotentialFarShellSet z r j
  have hU : MeasurableSet (⋃ j : ℕ, heatPotentialFarShellSet z r j) :=
    MeasurableSet.iUnion hT
  have hIntS : IntegrableOn f (heatPotentialNearSet z r) volume :=
    hInt.mono_set (subset_union_left)
  have hIntU : IntegrableOn f (⋃ j : ℕ, heatPotentialFarShellSet z r j) volume :=
    hInt.mono_set (subset_union_right)
  have hsplit : volume.restrict (heatPotentialNearSet z r ∪
      ⋃ j : ℕ, heatPotentialFarShellSet z r j) = volume.restrict (heatPotentialNearSet z r) +
      volume.restrict (⋃ j : ℕ, heatPotentialFarShellSet z r j) :=
    Measure.restrict_union (disjoint_iUnion_right.mpr hdST) hU
  calc
    ∫ v in heatPotentialNearSet z r ∪ ⋃ j : ℕ, heatPotentialFarShellSet z r j, f v =
        ∫ v, f v ∂(volume.restrict (heatPotentialNearSet z r ∪
          ⋃ j : ℕ, heatPotentialFarShellSet z r j)) := rfl
    _ = ∫ v, f v ∂(volume.restrict (heatPotentialNearSet z r) +
        volume.restrict (⋃ j : ℕ, heatPotentialFarShellSet z r j)) := by
      rw [hsplit]
    _ = (∫ v in heatPotentialNearSet z r, f v) +
        ∫ v in ⋃ j : ℕ, heatPotentialFarShellSet z r j, f v :=
      MeasureTheory.integral_add_measure hIntS hIntU
    _ = (∫ v in heatPotentialNearSet z r, f v) +
        ∑' j : ℕ, ∫ v in heatPotentialFarShellSet z r j, f v :=
      congrArg (fun x : ℝ => (∫ v in heatPotentialNearSet z r, f v) + x)
        (MeasureTheory.integral_iUnion hT hdT hIntU)

end CKN.Core.HeatPotential
