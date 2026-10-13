/-
Copyright (c) 2026 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara
-/
module

public import Tengoku.LeanPool.LeanPool.RiemannMappingTheorem.Cindex
import Tengoku.LeanPool.LeanPool.RiemannMappingTheorem.Hurwitz
public import Tengoku

/-!
# LeanPool.RiemannMappingTheorem.DerivInj
-/

@[expose] public section

open Complex Metric circleIntegral Topology Filter Set

variable {ι α β : Type*} {U : Set ℂ} {c z₀ : ℂ} {r : ℝ} {f g : ℂ → ℂ}

lemma crucial (hU : IsOpen U) (hcr : closedBall c r ⊆ U) (hz₀ : z₀ ∈ ball c r)
    (hf : DifferentiableOn ℂ f U)
    (hfz₀ : f z₀ = 0) (hf'z₀ : deriv f z₀ ≠ 0)
    (hfz : ∀ z ∈ closedBall c r, z ≠ z₀ → f z ≠ 0) :
    cindex c r f = 1 := by
  have hr : 0 < r := dist_nonneg.trans_lt hz₀
  set g := dslope f z₀
  have h1 : DifferentiableOn ℂ g U :=
    (differentiableOn_dslope (hU.mem_nhds (hcr (ball_subset_closedBall hz₀)))).2 hf
  have h2 : ∀ z ∈ closedBall c r, g z ≠ 0 := by
    rintro z hz
    by_cases h : z = z₀
    case pos => simp [g, dslope, h, hf'z₀]
    case neg => simp [g, dslope, h, slope, sub_ne_zero.2 h, hfz₀, hfz z hz h]
  have h10 : ∀ z ∈ sphere c r, z - z₀ ≠ 0 :=
    fun z hz => sub_ne_zero.2 (sphere_disjoint_ball.ne_of_mem hz hz₀)
  suffices this : cindex c r f =
      ((2 * Real.pi * I)⁻¹ * ∮ z in C(c, r), (z - z₀)⁻¹) + cindex c r g by
    rw [this, integral_sub_inv_of_mem_ball hz₀, cindex_eq_zero hU hr hcr h1 h2]
    field_simp
    ring
  have h6 : ∀ z ∈ sphere c r, deriv f z / f z = (z - z₀)⁻¹ + deriv g z / g z := by
    rintro z hz
    have h3 : ∀ z ∈ U, f z = (z - z₀) * g z :=
      fun z _ => by simpa only [smul_eq_mul, hfz₀, sub_zero] using (sub_smul_dslope f z₀ z).symm
    have hz' : z ∈ U := hcr (sphere_subset_closedBall hz)
    have e0 : U ∈ 𝓝 z := hU.mem_nhds hz'
    have h4 : deriv f z = deriv (fun w => (w - z₀) * g w) z :=
      EventuallyEq.deriv_eq (eventually_of_mem e0 h3)
    have e1 : DifferentiableAt ℂ (fun y => y - z₀) z := differentiableAt_id.sub_const z₀
    have e2 : DifferentiableAt ℂ g z := h1.differentiableAt e0
    have h5 : deriv f z = g z + (z - z₀) * deriv g z := by
      simp [h4, deriv_fun_mul e1 e2]
    have e3 : g z ≠ 0 := h2 z (sphere_subset_closedBall hz)
    have := h10 z hz
    field_simp
    simp [h3 z hz', h5, mul_comm]
    field_simp
  simp only [cindex, integral_congr hr.le h6, ← mul_add]
  congr
  apply circleIntegral.integral_add
  · rw [circleIntegrable_sub_inv_iff, abs_eq_self.2 hr.le]
    exact Or.inr (disjoint_right.1 sphere_disjoint_ball hz₀)
  · refine (ContinuousOn.div ?_ ?_ ?_).circleIntegrable hr.le
    · exact (h1.deriv hU).continuousOn.mono (sphere_subset_closedBall.trans hcr)
    · exact h1.continuousOn.mono (sphere_subset_closedBall.trans hcr)
    · exact fun z hz => h2 z (sphere_subset_closedBall hz)

lemma tendsto_uniformly_on_const {f : α → β} [UniformSpace β] {p : Filter ι} {s : Set α} :
    TendstoUniformlyOn (fun _ => f) f p s :=
  UniformOnFun.tendsto_iff_tendstoUniformlyOn.1 tendsto_const_nhds s (Set.mem_singleton _)

lemma bla (hf : AnalyticAt ℂ f z₀)
    (hf' : HasFPowerSeriesAt (deriv f) (0 : FormalMultilinearSeries ℂ ℂ ℂ) z₀) :
    ∀ᶠ z in 𝓝 z₀, f z = f z₀ := by
  have h1 : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ f z := (isOpen_analyticAt ℂ f).mem_nhds hf
  obtain ⟨ε, hε, h⟩ := Metric.mem_nhds_iff.1 (h1.and hf'.eventually_eq_zero)
  refine Metric.mem_nhds_iff.2 ⟨ε, hε, fun z hz => ?_⟩
  have h3 : ∀ z ∈ ball z₀ ε, fderivWithin ℂ f (ball z₀ ε) z = 0 := by
    rintro z hz
    rw [fderivWithin_eq_fderiv (isOpen_ball.uniqueDiffWithinAt hz) ((h hz).1.differentiableAt)]
    ext1
    simpa [fderiv_apply_one_eq_deriv] using (h hz).2
  have h4 : DifferentiableOn ℂ f (ball z₀ ε) := fun z hz => (h hz).1.differentiableWithinAt
  exact Convex.is_const_of_fderivWithin_eq_zero (convex_ball z₀ ε) h4 h3 hz (mem_ball_self hε)

lemma two_le_order_of_deriv_eq_zero {g : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hgp : HasFPowerSeriesAt g p z₀) (hp : p ≠ 0) (hg : g z₀ = 0) (hg' : deriv g z₀ = 0) :
    2 ≤ p.order := by
  classical
  have h1 : p.coeff 1 = 0 := by
    rw [FormalMultilinearSeries.coeff]
    change (p 1) (fun _ => (1 : ℂ)) = 0
    simpa only [hg'] using hgp.deriv.symm
  have h2 : p 0 = 0 := by
    ext1
    change (p 0) (fun _ => (1 : ℂ)) = 0
    simpa only [hg] using hgp.coeff_zero (fun _ => (1 : ℂ))
  have h3 : p 1 = 0 := by ext1; simp [h1]
  rw [FormalMultilinearSeries.order_eq_find' hp, Nat.le_find_iff]
  intro n hn
  cases n
  case zero => simp [h2]
  case succ n =>
    cases n
    case zero => simpa using h3
    case succ => linarith
