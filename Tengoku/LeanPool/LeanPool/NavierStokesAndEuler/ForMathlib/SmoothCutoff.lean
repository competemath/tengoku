/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Code4me2
-/

module

public import Tengoku

/-!
# The dilated radius-1-to-2 bump cutoff

This family supports localization arguments in real inner-product spaces:
one fixed `ContDiffBump` that equals one on the closed unit ball and vanishes
outside the ball of radius two, dilated to `cutoff E R x = χ (R⁻¹ • x)`.
Because every member of the family is a dilation of the same bump, its
derivative bounds have `R`-independent constants:
`‖iteratedFDeriv ℝ n (cutoff E R) x‖ ≤ derivativeConstant E n / R ^ n`, and the
scale-invariant `‖fderiv ℝ (cutoff E R) x‖ * ‖x‖ ≤ 2 * derivativeConstant E 1`.

The space is an explicit argument of the definitions so that partial applications
such as `cutoff E R` elaborate without an expected type. The derivative constant
is accessed through its positivity and bound lemmas; its choice is private.
-/

public section

noncomputable section

open Set Filter Metric
open scoped ContDiff Topology

namespace NavierStokesAndEuler.SmoothCutoff

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The fixed bump with inner radius one and outer radius two. -/
@[expose] def baseBump : ContDiffBump (0 : E) :=
  ⟨1, 2, by norm_num, by norm_num⟩

/-- The unscaled cutoff. -/
@[expose] def baseCutoff (x : E) : ℝ := baseBump E x

/-- The cutoff at spatial radius `R`; its estimates are stated for `0 < R`. -/
@[expose] def cutoff (R : ℝ) (x : E) : ℝ := baseCutoff E (R⁻¹ • x)

variable {E}

/--
@isnad1 id=contdiff.0h1v.s5.1c35056359bd from=translated src=- shape=b7aa571f vocab=e3dc4549
-/
theorem baseCutoff_smooth : ContDiff ℝ ∞ (baseCutoff E) := (baseBump E).contDiff

/--
@isnad1 id=le.0h2v.s4.98390918a284 from=translated src=- shape=f9172607 vocab=5f92080a
-/
theorem baseCutoff_nonneg (x : E) : 0 ≤ baseCutoff E x := (baseBump E).nonneg

/--
@isnad1 id=le.0h2v.s4.09c4e6e2a15f from=translated src=- shape=f5fe6afa vocab=5f92080a
-/
theorem baseCutoff_le_one (x : E) : baseCutoff E x ≤ 1 := (baseBump E).le_one

/--
@isnad1 id=eq.1h2v.s5.a929650e41f1 from=translated src=- shape=a81fac26 vocab=e587b5dd
-/
theorem baseCutoff_eq_one {x : E} (hx : ‖x‖ ≤ 1) : baseCutoff E x = 1 := by
  apply (baseBump E).one_of_mem_closedBall
  simpa [baseBump, mem_closedBall, dist_zero_right] using hx

/--
@isnad1 id=eq.1h2v.s5.8fbe26fc7da9 from=translated src=- shape=a677f6ee vocab=0e376c98
-/
theorem baseCutoff_eq_zero {x : E} (hx : 2 ≤ ‖x‖) : baseCutoff E x = 0 := by
  apply (baseBump E).zero_of_le_dist
  simpa [baseBump, dist_zero_right] using hx

/--
@isnad1 id=contdiff.0h2v.s5.92f79316fdb6 from=translated src=- shape=8e545e77 vocab=967c257b
-/
theorem cutoff_smooth (R : ℝ) : ContDiff ℝ ∞ (cutoff E R) :=
  baseCutoff_smooth.comp (contDiff_id.const_smul R⁻¹)

/--
@isnad1 id=le.0h3v.s5.3dde13d5c93e from=translated src=- shape=30c3b130 vocab=fb133b08
-/
theorem cutoff_nonneg (R : ℝ) (x : E) : 0 ≤ cutoff E R x :=
  baseCutoff_nonneg _

/--
@isnad1 id=le.0h3v.s5.428eaba975c8 from=translated src=- shape=b1bf4ff3 vocab=fb133b08
-/
theorem cutoff_le_one (R : ℝ) (x : E) : cutoff E R x ≤ 1 :=
  baseCutoff_le_one _

/--
@isnad1 id=mem.0h3v.s5.f0b2f8c63c48 from=translated src=- shape=162aa790 vocab=24309d4a
-/
theorem cutoff_mem_Icc (R : ℝ) (x : E) : cutoff E R x ∈ Icc (0 : ℝ) 1 :=
  ⟨cutoff_nonneg R x, cutoff_le_one R x⟩

/--
@isnad1 id=le.0h3v.s5.4e7e3345e2de from=translated src=- shape=df6cae73 vocab=918e8fbb
-/
theorem norm_cutoff_le_one (R : ℝ) (x : E) : ‖cutoff E R x‖ ≤ 1 := by
  rw [Real.norm_of_nonneg (cutoff_nonneg R x)]
  exact cutoff_le_one R x

/--
@isnad1 id=eq.1h3v.s7.a16c8db25d1a from=translated src=- shape=fc4edb22 vocab=c2154749
-/
theorem norm_inv_smul {R : ℝ} (hR : 0 < R) (x : E) : ‖R⁻¹ • x‖ = ‖x‖ / R := by
  simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR, div_eq_inv_mul]

/--
@isnad1 id=eq.2h3v.s5.462528ce0f9b from=translated src=- shape=370a3aeb vocab=94156bcc
-/
theorem cutoff_eq_one {R : ℝ} (hR : 0 < R) {x : E} (hx : ‖x‖ ≤ R) :
    cutoff E R x = 1 := by
  apply baseCutoff_eq_one
  rw [norm_inv_smul hR, div_le_one hR]
  exact hx

/--
@isnad1 id=eq.2h3v.s6.fee7afdc1a1f from=translated src=- shape=d7b8cdf1 vocab=66b5d8bb
-/
theorem cutoff_eq_zero {R : ℝ} (hR : 0 < R) {x : E} (hx : 2 * R ≤ ‖x‖) :
    cutoff E R x = 0 := by
  apply baseCutoff_eq_zero
  rw [norm_inv_smul hR, le_div_iff₀ hR]
  exact hx

/--
@isnad1 id=le.1h2v.s6.057c47116d34 from=translated src=- shape=35294952 vocab=38a3648f
-/
theorem cutoff_support_subset {R : ℝ} (hR : 0 < R) :
    Function.support (cutoff E R) ⊆ ball (0 : E) (2 * R) := by
  intro x hx
  by_contra h
  apply hx
  exact cutoff_eq_zero hR (by simpa [mem_ball, dist_zero_right, not_lt] using h)

/--
@isnad1 id=le.1h2v.s6.d4dd9e0331d2 from=translated src=- shape=35294952 vocab=692408c8
-/
theorem cutoff_tsupport_subset {R : ℝ} (hR : 0 < R) :
    tsupport (cutoff E R) ⊆ closedBall (0 : E) (2 * R) :=
  closure_minimal ((cutoff_support_subset hR).trans ball_subset_closedBall) isClosed_closedBall

/-- Near any point of the open ball of radius `R` the cutoff is identically one.
@isnad1 id=eventual.2h3v.s6.0d7c7701b634 from=translated src=- shape=8195e4d4 vocab=a283393e
-/
theorem cutoff_eventuallyEq_one {R : ℝ} (hR : 0 < R) {x : E} (hx : ‖x‖ < R) :
    cutoff E R =ᶠ[𝓝 x] 1 := by
  filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds hx)] with y hy
  exact cutoff_eq_one hR hy.le

/-! ### Plateaus -/

/-- Every bounded set lies in the plateau of all sufficiently large cutoffs.
@isnad1 id=ex.1h2v.s6.0dd3eda2e583 from=translated src=- shape=af386b85 vocab=0e034b1b
-/
theorem bounded_plateau {K : Set E} (hK : Bornology.IsBounded K) :
    ∃ R₀ > 0, ∀ R ≥ R₀, EqOn (cutoff E R) (fun _ => 1) K := by
  obtain ⟨R₀, hR₀, hbound⟩ := hK.exists_pos_norm_le
  exact ⟨R₀, hR₀, fun R hR x hx => cutoff_eq_one (hR₀.trans_le hR)
    ((hbound x hx).trans hR)⟩

/-- On a fixed bounded set the cutoffs eventually agree with the constant one.
@isnad1 id=eventual.1h2v.s5.83c94946f1ed from=translated src=- shape=b4cd8930 vocab=6ebfff29
-/
theorem eventually_bounded_plateau {K : Set E} (hK : Bornology.IsBounded K) :
    ∀ᶠ R : ℝ in atTop, EqOn (cutoff E R) (fun _ => 1) K := by
  obtain ⟨R₀, _, h⟩ := bounded_plateau hK
  exact eventually_atTop.2 ⟨R₀, h⟩

/-- Every fixed compact set lies in the plateau of all sufficiently large cutoffs.
@isnad1 id=ex.1h2v.s6.d2bfb5833a18 from=translated src=- shape=af386b85 vocab=13426383
-/
theorem compact_plateau {K : Set E} (hK : IsCompact K) :
    ∃ R₀ > 0, ∀ R ≥ R₀, EqOn (cutoff E R) (fun _ => 1) K :=
  bounded_plateau hK.isBounded

/--
@isnad1 id=eventual.1h2v.s5.9e946cf6dc74 from=translated src=- shape=b4cd8930 vocab=155a9f58
-/
theorem eventually_compact_plateau {K : Set E} (hK : IsCompact K) :
    ∀ᶠ R : ℝ in atTop, EqOn (cutoff E R) (fun _ => 1) K := by
  obtain ⟨R₀, _, h⟩ := compact_plateau hK
  exact eventually_atTop.2 ⟨R₀, h⟩

/--
@isnad1 id=eventual.0h2v.s5.4cf1d48ed8d1 from=translated src=- shape=ff3c8103 vocab=e2f9d8fe
-/
theorem eventually_cutoff_eq_one (x : E) :
    ∀ᶠ R : ℝ in atTop, cutoff E R x = 1 := by
  filter_upwards [eventually_compact_plateau (isCompact_singleton (x := x))] with R hR
  exact hR (mem_singleton x)

/--
@isnad1 id=tendsto.0h2v.s5.3fce718ce6d2 from=translated src=- shape=1e61c15e vocab=7fbdb612
-/
theorem cutoff_tendsto_one (x : E) :
    Tendsto (fun R : ℝ => cutoff E R x) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_cutoff_eq_one x] with R hR
  exact hR.symm

/-! ### Derivative bounds under dilation -/

section Dilation

variable {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The dilation `x ↦ R⁻¹ • x` as a continuous linear map. -/
private def dilation (D : Type*) [NormedAddCommGroup D] [NormedSpace ℝ D] (R : ℝ) :
    D →L[ℝ] D :=
  R⁻¹ • ContinuousLinearMap.id ℝ D

end Dilation

/-! ### Compact support

From here on the space is finite-dimensional, so the closed balls containing the
supports are compact and every derivative of the bump is bounded. -/

variable [FiniteDimensional ℝ E]

/--
@isnad1 id=hascompa.0h1v.s5.0f414aee51ff from=translated src=- shape=70ededd8 vocab=d7377b56
-/
theorem baseCutoff_hasCompactSupport : HasCompactSupport (baseCutoff E) :=
  (baseBump E).hasCompactSupport

/--
@isnad1 id=hascompa.1h2v.s6.dc397104d076 from=translated src=- shape=c1f9584f vocab=5ef4d118
-/
theorem cutoff_hasCompactSupport {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (cutoff E R) :=
  (isCompact_closedBall (0 : E) (2 * R)).of_isClosed_subset
    isClosed_closure (cutoff_tsupport_subset hR)

private theorem exists_derivative_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : E, ‖iteratedFDeriv ℝ n (baseCutoff E) x‖ ≤ C := by
  have hc : HasCompactSupport (iteratedFDeriv ℝ n (baseCutoff E)) :=
    baseCutoff_hasCompactSupport.iteratedFDeriv n
  have hcont : Continuous (iteratedFDeriv ℝ n (baseCutoff E)) :=
    ContDiff.continuous_iteratedFDeriv le_rfl (contDiff_infty.1 baseCutoff_smooth n)
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hcont
  exact ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    fun x => (hC x).trans (le_max_right _ _)⟩

variable (E) in
/-- A fixed positive bound for the `n`th derivative of the unscaled bump. -/
def derivativeConstant (n : ℕ) : ℝ := Classical.choose (exists_derivative_bound (E := E) n)

/--
@isnad1 id=lt.0h2v.s5.e42241790047 from=translated src=- shape=91835d9e vocab=a00469ab
-/
theorem derivativeConstant_pos (n : ℕ) : 0 < derivativeConstant E n :=
  (Classical.choose_spec (exists_derivative_bound (E := E) n)).1

/--
@isnad1 id=le.0h3v.s7.c796f1ed7502 from=translated src=- shape=0684968c vocab=beca752d
-/
theorem baseCutoff_iteratedFDeriv_le (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (baseCutoff E) x‖ ≤ derivativeConstant E n :=
  (Classical.choose_spec (exists_derivative_bound (E := E) n)).2 x

end NavierStokesAndEuler.SmoothCutoff
