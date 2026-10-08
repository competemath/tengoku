/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Calculus.BumpFunction.Basic
public import Tengoku.Seed.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Normed bump function

In this file we define `ContDiffBump.normed f μ` to be the bump function `f` normalized so that
`∫ x, f.normed μ x ∂μ = 1` and prove some properties of this function.
-/

@[expose] public section

noncomputable section

open Function Filter Set Metric MeasureTheory Module Measure
open scoped Topology

namespace ContDiffBump

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]
  [MeasurableSpace E] {c : E} (f : ContDiffBump c) {x : E} {n : ℕ∞} {μ : Measure E}

/-- A bump function normed so that `∫ x, f.normed μ x ∂μ = 1`. -/
protected def normed (μ : Measure E) : E → ℝ := fun x => f x / ∫ x, f x ∂μ

/--
@isnad1 id=eq.0h5v.s6.52de3aef2006 from=seed src=0 shape=339d8765 vocab=b10e0b48
-/
theorem normed_def {μ : Measure E} (x : E) : f.normed μ x = f x / ∫ x, f x ∂μ :=
  rfl

/--
@isnad1 id=le.0h5v.s5.5f7e5c8c4d2b from=seed src=0 shape=d1364fb0 vocab=b4310f22
-/
theorem nonneg_normed (x : E) : 0 ≤ f.normed μ x :=
  div_nonneg f.nonneg <| integral_nonneg f.nonneg'

/--
@isnad1 id=contdiff.0h5v.s6.8ab3d7642b6d from=seed src=0 shape=f25042ba vocab=0004cf0f
-/
theorem contDiff_normed {n : ℕ∞} : ContDiff ℝ n (f.normed μ) :=
  f.contDiff.div_const _

/--
@isnad1 id=continuo.0h4v.s5.77a6275c2b78 from=seed src=0 shape=c58e930b vocab=50b50fc4
-/
theorem continuous_normed : Continuous (f.normed μ) :=
  f.continuous.div_const _

/--
@isnad1 id=eq.0h5v.s6.a9e508a77d0f from=seed src=0 shape=1b70e0b1 vocab=4890668e
-/
theorem normed_sub (x : E) : f.normed μ (c - x) = f.normed μ (c + x) := by
  simp_rw [f.normed_def, f.sub]

/--
@isnad1 id=eq.0h4v.s6.15c5242b5986 from=seed src=0 shape=7000b22b vocab=562af561
-/
theorem normed_neg (f : ContDiffBump (0 : E)) (x : E) : f.normed μ (-x) = f.normed μ x := by
  simp_rw [f.normed_def, f.neg]

variable [BorelSpace E] [FiniteDimensional ℝ E] [IsLocallyFiniteMeasure μ]

/--
@isnad1 id=integrab.0h4v.s6.c486c12fa790 from=seed src=0 shape=a881a6ed vocab=079e4b20
-/
protected theorem integrable : Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport

/--
@isnad1 id=integrab.0h4v.s6.7fdc5554cf56 from=seed src=0 shape=316fdc0a vocab=1d6bad72
-/
protected theorem integrable_normed : Integrable (f.normed μ) μ :=
  f.integrable.div_const _

section
variable [μ.IsOpenPosMeasure]

/--
@isnad1 id=lt.0h4v.s6.15b77f96d33e from=seed src=0 shape=503eb3de vocab=c95bd183
-/
theorem integral_pos : 0 < ∫ x, f x ∂μ := by
  refine (integral_pos_iff_support_of_nonneg f.nonneg' f.integrable).mpr ?_
  rw [f.support_eq]
  exact measure_ball_pos μ c f.rOut_pos

/--
@isnad1 id=eq.0h4v.s6.69bfa285b26d from=seed src=0 shape=139ec86a vocab=f4ba9027
-/
theorem integral_normed : ∫ x, f.normed μ x ∂μ = 1 := by
  simp_rw [ContDiffBump.normed, div_eq_mul_inv, mul_comm (f _), ← smul_eq_mul, integral_smul]
  exact inv_mul_cancel₀ f.integral_pos.ne'

/--
@isnad1 id=eq.0h4v.s6.d3c2cf5580cf from=seed src=0 shape=a7a3f768 vocab=5da71210
-/
theorem support_normed_eq : Function.support (f.normed μ) = Metric.ball c f.rOut := by
  unfold ContDiffBump.normed
  rw [support_div, f.support_eq, support_const f.integral_pos.ne', inter_univ]

/--
@isnad1 id=eq.0h4v.s6.29816e67602f from=seed src=0 shape=a7a3f768 vocab=a4a81d48
-/
theorem tsupport_normed_eq : tsupport (f.normed μ) = Metric.closedBall c f.rOut := by
  rw [tsupport, f.support_normed_eq, closure_ball _ f.rOut_pos.ne']

/--
@isnad1 id=hascompa.0h4v.s6.70d5fc3a9c00 from=seed src=0 shape=77a9360f vocab=ad9035e1
-/
theorem hasCompactSupport_normed : HasCompactSupport (f.normed μ) := by
  simp only [HasCompactSupport, f.tsupport_normed_eq (μ := μ), isCompact_closedBall]

/--
@isnad1 id=tendsto.1h6v.s7.9f62772f06e5 from=seed src=0 shape=87d8005b vocab=62edffab
-/
theorem tendsto_support_normed_smallSets {ι} {φ : ι → ContDiffBump c} {l : Filter ι}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) :
    Tendsto (fun i => Function.support fun x => (φ i).normed μ x) l (𝓝 c).smallSets := by
  simp_rw [NormedAddGroup.tendsto_nhds_zero, Real.norm_eq_abs,
    abs_eq_self.mpr (φ _).rOut_pos.le] at hφ
  rw [nhds_basis_ball.smallSets.tendsto_right_iff]
  refine fun ε hε ↦ (hφ ε hε).mono fun i hi ↦ ?_
  rw [(φ i).support_normed_eq]
  exact ball_subset_ball hi.le

variable (μ)

/--
@isnad1 id=eq.0h6v.s7.08fd4195f5d3 from=seed src=0 shape=e60a8bb7 vocab=0f5e7e59
-/
theorem integral_normed_smul {X} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (z : X) : ∫ x, f.normed μ x • z ∂μ = z := by
  simp_rw [integral_smul_const, f.integral_normed (μ := μ), one_smul]

end

variable (μ)

/--
@isnad1 id=le.0h4v.s6.fba2401de8e6 from=seed src=0 shape=00919b72 vocab=265f4f4d
-/
theorem measure_closedBall_le_integral : μ.real (closedBall c f.rIn) ≤ ∫ x, f x ∂μ := by calc
  μ.real (closedBall c f.rIn) = ∫ x in closedBall c f.rIn, 1 ∂μ := by simp
  _ = ∫ x in closedBall c f.rIn, f x ∂μ := setIntegral_congr_fun measurableSet_closedBall
        (fun x hx ↦ (one_of_mem_closedBall f hx).symm)
  _ ≤ ∫ x, f x ∂μ := setIntegral_le_integral f.integrable (Eventually.of_forall (fun x ↦ f.nonneg))

/--
@isnad1 id=le.0h5v.s7.eae4c0a4c930 from=seed src=0 shape=5bf3ca29 vocab=d1f8d79b
-/
theorem normed_le_div_measure_closedBall_rIn [μ.IsOpenPosMeasure] (x : E) :
    f.normed μ x ≤ 1 / μ.real (closedBall c f.rIn) := by
  rw [normed_def]
  gcongr
  · exact ENNReal.toReal_pos (measure_closedBall_pos _ _ f.rIn_pos).ne' measure_closedBall_lt_top.ne
  · exact f.le_one
  · exact f.measure_closedBall_le_integral μ

/--
@isnad1 id=le.0h4v.s6.e13693a3c3ae from=seed src=0 shape=0a9a0f72 vocab=d675042f
-/
theorem integral_le_measure_closedBall : ∫ x, f x ∂μ ≤ μ.real (closedBall c f.rOut) := by calc
  ∫ x, f x ∂μ = ∫ x in closedBall c f.rOut, f x ∂μ := by
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ ?_)).symm
    apply f.zero_of_le_dist (le_of_lt _)
    simpa using hx
  _ ≤ ∫ x in closedBall c f.rOut, 1 ∂μ := by
    apply setIntegral_mono f.integrable.integrableOn _ (fun x ↦ f.le_one)
    simp [measure_closedBall_lt_top]
  _ = μ.real (closedBall c f.rOut) := by simp

/--
@isnad1 id=le.1h5v.s7.d06d62db0102 from=seed src=0 shape=5b461c68 vocab=36db114e
-/
theorem measure_closedBall_div_le_integral [IsAddHaarMeasure μ] (K : ℝ) (h : f.rOut ≤ K * f.rIn) :
    μ.real (closedBall c f.rOut) / K ^ finrank ℝ E ≤ ∫ x, f x ∂μ := by
  have K_pos : 0 < K := by
    simpa [f.rIn_pos, not_lt.2 f.rIn_pos.le] using mul_pos_iff.1 (f.rOut_pos.trans_le h)
  apply le_trans _ (f.measure_closedBall_le_integral μ)
  rw [div_le_iff₀ (pow_pos K_pos _), addHaar_real_closedBall' _ _ f.rIn_pos.le,
    addHaar_real_closedBall' _ _ f.rOut_pos.le, mul_assoc, mul_comm _ (K ^ _), ← mul_assoc,
    ← mul_pow, mul_comm _ K]
  gcongr
  exact f.rOut_pos.le

/--
@isnad1 id=le.1h6v.s7.05dc83bf8fe4 from=seed src=0 shape=37708c36 vocab=27870510
-/
theorem normed_le_div_measure_closedBall_rOut [IsAddHaarMeasure μ] (K : ℝ) (h : f.rOut ≤ K * f.rIn)
    (x : E) :
    f.normed μ x ≤ K ^ finrank ℝ E / μ.real (closedBall c f.rOut) := by
  have K_pos : 0 < K := by
    simpa [f.rIn_pos, not_lt.2 f.rIn_pos.le] using mul_pos_iff.1 (f.rOut_pos.trans_le h)
  have : f x / ∫ y, f y ∂μ ≤ 1 / ∫ y, f y ∂μ := by
    gcongr
    · exact f.integral_pos.le
    · exact f.le_one
  apply this.trans
  rw [div_le_div_iff₀ f.integral_pos, one_mul, ← div_le_iff₀' (pow_pos K_pos _)]
  · exact f.measure_closedBall_div_le_integral μ K h
  · exact ENNReal.toReal_pos (measure_closedBall_pos _ _ f.rOut_pos).ne'
      measure_closedBall_lt_top.ne

end ContDiffBump
