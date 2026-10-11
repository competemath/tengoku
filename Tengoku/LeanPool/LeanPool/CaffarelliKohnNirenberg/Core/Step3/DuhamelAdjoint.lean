/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalEquationRepresentation
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.BackwardPotentialKernelBridge
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.SpaceTime

/-!
# Duhamel Adjoint

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

noncomputable section

namespace CKN.Core.Step3

open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Core.HeatPotential

theorem canonical_spaceTime_cutoff_box {r R t₀ : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) :
    let χ : Vec3 × ℝ → ℝ := CKN.spaceTimeCutoff (0 : Vec3) t₀ r R
    χ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ ∧
      (∀ z : Vec3 × ℝ, z.1 ∈ euclideanBall (0 : Vec3) r →
        z.2 ∈ Icc (t₀ - r ^ 2) t₀ → χ z = 1) := by
  dsimp
  let χ : Vec3 × ℝ → ℝ := CKN.spaceTimeCutoff (0 : Vec3) t₀ r R
  have hχdiff : ContDiff ℝ (⊤ : ℕ∞) χ := by
    exact spaceTimeCutoff_smooth (0 : Vec3) t₀ r R hr hrR
  have hχcompact : HasCompactSupport χ := by
    apply HasCompactSupport.intro
      (show IsCompact (euclideanClosedBall (0 : Vec3) R ×ˢ
        Icc (t₀ - R ^ 2) (t₀ + (R ^ 2 - r ^ 2))) from
          (isCompact_euclideanClosedBall (0 : Vec3) (R := R)
            (lt_of_le_of_lt hr hrR).le).prod isCompact_Icc)
    intro z hz
    by_contra hne
    have hsupp : z ∈ Function.support χ := hne
    have hout := spaceTimeCutoff_support_subset
      (x₀ := (0 : Vec3)) (t₀ := t₀) (r := r) (R := R) hr hrR hsupp
    by_cases hzx : z.1 ∈ euclideanClosedBall (0 : Vec3) R
    · by_cases hzt : z.2 ∈ Icc (t₀ - R ^ 2) (t₀ + (R ^ 2 - r ^ 2))
      · exact hz ⟨hzx, hzt⟩
      · exact hzt ⟨le_of_lt hout.2.1, le_of_lt hout.2.2⟩
    · apply hzx
      change euclideanSqDist z.1 0 ≤ R ^ 2
      exact le_of_lt hout.1
  have hχsupport : tsupport χ ⊆ spaceTimeSet Set.univ Set.univ := by
    simp [spaceTimeSet]
  refine ⟨⟨hχdiff, hχcompact, hχsupport⟩, ?_⟩
  intro z hzx hzt
  exact spaceTimeCutoff_eq_one_on hr hrR hzx hzt

/-! The causal heat potential with a divergence-form source. -/

/-- Vector Duhamel potential with the sign convention for the localized divergence equation. -/
def duhamelPotential (g : ParabolicPoint → Vec3)
    (h : Fin 3 → ParabolicPoint → Vec3) (z : ParabolicPoint) : Vec3 :=
  fun i =>
    (∫ v, heatPotentialKernel z v * g v i) -
      ∑ j, ∫ v, heatPotentialSpatialKernel j z v * h j v i

/-- Common interior cylinder containing the supports needed for the localized Duhamel argument. -/
structure DuhamelSupportData
    (v g : ParabolicPoint → Vec3)
    (h : Fin 3 → ParabolicPoint → Vec3) where
  /-- Inner radius on which the common Duhamel cutoff is one. -/
  r : ℝ
  /-- Outer radius containing the supports of all localized sources. -/
  R : ℝ
  /-- Reference time for the common Duhamel support cylinder. -/
  t₀ : ℝ
  hr : 0 ≤ r
  hrR : r < R
  v_support : ∀ i : Fin 3, ∀ z ∈ tsupport (fun w => v w i),
    z.1 ∈ euclideanBall (0 : Vec3) r ∧ z.2 ∈ Ioo (t₀ - r ^ 2) t₀
  g_support : ∀ i : Fin 3, ∀ z ∈ tsupport (fun w => g w i),
    z.1 ∈ euclideanBall (0 : Vec3) r ∧ z.2 ∈ Ioo (t₀ - r ^ 2) t₀
  h_support : ∀ j i : Fin 3, ∀ z ∈ tsupport (fun w => h j w i),
    z.1 ∈ euclideanBall (0 : Vec3) r ∧ z.2 ∈ Ioo (t₀ - r ^ 2) t₀

theorem duhamelPotential_pairing
    {ζ : ParabolicPoint → ℝ} {g : ParabolicPoint → Vec3}
    {h : Fin 3 → ParabolicPoint → Vec3} (i : Fin 3)
    (hFg : Integrable (fun q : ParabolicPoint × ParabolicPoint =>
      backwardHeatKernel q.1 q.2 * ζ q.1 * g q.2 i)
      ((volume : Measure ParabolicPoint).prod volume))
    (hFh : ∀ j : Fin 3, Integrable (fun q : ParabolicPoint × ParabolicPoint =>
      backwardHeatSpatialKernel j q.1 q.2 * ζ q.1 * h j q.2 i)
      ((volume : Measure ParabolicPoint).prod volume)) :
    ∫ z, ζ z * duhamelPotential g h z i =
      (∫ v, g v i * backwardHeatPotential ζ v) +
        ∑ j, (∫ v, h j v i * backwardHeatPotentialSpatial j ζ v) := by
  let _ : SFinite (volume : Measure ParabolicPoint) := by
    rw [Integration.volume_parabolicPoint_eq_prod]
    exact Measure.prod.instSFinite
  have hleftG : Integrable (fun z =>
      ζ z * (∫ v, backwardHeatKernel z v * g v i)) volume := by
    have hh := hFg.integral_prod_left
    apply hh.congr
    filter_upwards [] with z
    rw [show (∫ v, backwardHeatKernel z v * ζ z * g v i) =
        ∫ v, ζ z * (backwardHeatKernel z v * g v i) by
          apply integral_congr_ae
          filter_upwards [] with v
          ring, integral_const_mul]
  have hrightG : Integrable (fun v =>
      g v i * (∫ z, backwardHeatKernel z v * ζ z)) volume := by
    have hh := hFg.integral_prod_right
    apply hh.congr
    filter_upwards [] with v
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    ring
  have hleftH : ∀ j, Integrable (fun z =>
      ζ z * (∫ v, backwardHeatSpatialKernel j z v * h j v i)) volume := by
    intro j
    have hh := (hFh j).integral_prod_left
    apply hh.congr
    filter_upwards [] with z
    rw [show (∫ v, backwardHeatSpatialKernel j z v * ζ z * h j v i) =
        ∫ v, ζ z * (backwardHeatSpatialKernel j z v * h j v i) by
          apply integral_congr_ae
          filter_upwards [] with v
          ring, integral_const_mul]
  have hrightH : ∀ j, Integrable (fun v =>
      h j v i * (∫ z, backwardHeatSpatialKernel j z v * ζ z)) volume := by
    intro j
    have hh := (hFh j).integral_prod_right
    apply hh.congr
    filter_upwards [] with v
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    ring
  have hsumleft : Integrable (fun z =>
      ∑ j, ζ z * (∫ v, backwardHeatSpatialKernel j z v * h j v i)) volume :=
    integrable_finsetSum Finset.univ (fun j hj => hleftH j)
  unfold duhamelPotential
  change ∫ z, ζ z * ((∫ v, backwardHeatKernel z v * g v i) -
      ∑ j, ∫ v, backwardHeatSpatialKernel j z v * h j v i) = _
  have hrewrite : (fun z => ζ z * ((∫ v, backwardHeatKernel z v * g v i) -
      ∑ j, ∫ v, backwardHeatSpatialKernel j z v * h j v i)) =
      (fun z => ζ z * (∫ v, backwardHeatKernel z v * g v i) -
        ∑ j, ζ z * (∫ v, backwardHeatSpatialKernel j z v * h j v i)) := by
    funext z
    rw [mul_sub, Finset.mul_sum]
  rw [hrewrite, integral_sub hleftG hsumleft,
    integral_finsetSum Finset.univ (fun j hj => hleftH j)]
  have hg := backwardHeatPotential_pairing (f := fun v => g v i)
    (ζ := ζ) hFg
  have hh := fun j => backwardHeatPotential_spatial_pairing
    (i := j) (f := fun v => h j v i) (ζ := ζ) (hF := hFh j)
  have hleftG' : (∫ z, ζ z * (∫ v, backwardHeatKernel z v * g v i)) =
      ∫ v, g v i * backwardHeatPotential ζ v := by
    calc
      (∫ z, ζ z * (∫ v, backwardHeatKernel z v * g v i)) =
          ∫ z, (∫ v, backwardHeatKernel z v * g v i) * ζ z := by
        apply integral_congr_ae
        filter_upwards [] with z
        ring
      _ = ∫ v, g v i * backwardHeatPotential ζ v := hg.symm
  have hleftH' : ∀ j, (∫ z, ζ z * (∫ v,
      backwardHeatSpatialKernel j z v * h j v i)) =
      -∫ v, h j v i * backwardHeatPotentialSpatial j ζ v := by
    intro j
    calc
      (∫ z, ζ z * (∫ v, backwardHeatSpatialKernel j z v * h j v i)) =
          ∫ z, (∫ v, backwardHeatSpatialKernel j z v * h j v i) * ζ z := by
        apply integral_congr_ae
        filter_upwards [] with z
        ring
      _ = -∫ v, h j v i * backwardHeatPotentialSpatial j ζ v := by
        rw [hh j]
        ring
  rw [hleftG']
  rw [show (∑ j, ∫ z, ζ z * (∫ v,
      backwardHeatSpatialKernel j z v * h j v i)) =
      ∑ j, (-∫ v, h j v i * backwardHeatPotentialSpatial j ζ v) by
        apply Finset.sum_congr rfl
        intro j hj
        exact hleftH' j]
  rw [Finset.sum_neg_distrib]
  simp only [sub_neg_eq_add]

theorem duhamel_of_adjoint_identity
    {v g : ParabolicPoint → Vec3}
    {h : Fin 3 → ParabolicPoint → Vec3}
    (hv : ∀ i : Fin 3,
      LocallyIntegrable (fun z : Vec3 × ℝ => v z i)
        (volume : Measure (Vec3 × ℝ)))
    (hpotential : ∀ i : Fin 3,
      LocallyIntegrable (fun z : Vec3 × ℝ => duhamelPotential g h z i)
        (volume : Measure (Vec3 × ℝ)))
    (hadjoint : ∀ (ζ : Vec3 × ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) ζ →
      HasCompactSupport ζ → ∀ i : Fin 3,
        (∫ z : Vec3 × ℝ, ζ z * v z i) =
          ∫ z : Vec3 × ℝ, ζ z * duhamelPotential g h z i) :
    ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)),
      v z = duhamelPotential g h z := by
  have hcoord : ∀ i : Fin 3,
      ∀ᵐ z ∂volume, v z i = duhamelPotential g h z i := by
    intro i
    apply ae_eq_of_integral_contDiff_smul_eq (hv i) (hpotential i)
    intro ζ hζ hζc
    have h := hadjoint ζ hζ hζc i
    simpa only [smul_eq_mul] using h
  filter_upwards [hcoord 0, hcoord 1, hcoord 2] with z h0 h1 h2
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

end CKN.Core.Step3
