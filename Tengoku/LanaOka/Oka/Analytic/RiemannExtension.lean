/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.Seed.Analysis.Complex.RemovableSingularity
import Tengoku.LanaOka.Oka.Analytification.GAGA.ParametricIntervalIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Riemann extension theorem in several complex variables

Let `E` be a finite-dimensional complex normed space, `U ⊆ E` open and `g` holomorphic on `U`
such that the zero set of `g` in `U` has empty interior. A function that is holomorphic on
`U \ g ⁻¹' {0}` and locally bounded near every point of `U` extends uniquely to a holomorphic
function on `U`.

## Main results

- `differentiableOn_circleIntegral`: a circle integral depending holomorphically on a parameter
  in a finite-dimensional complex space is holomorphic in the parameter.
- `exists_differentiableOn_eqOn_of_isolated`: the one-variable Riemann extension theorem across a
  set of isolated points.
- `exists_differentiableOn_eqOn_of_isBoundedUnder`: **Riemann extension theorem.**
- `Set.EqOn.of_eqOn_diff_zero`: uniqueness of the extension.
- `DifferentiableOn.of_continuousOn_of_differentiableOn_diff_zero`: a function continuous on `U`
  and holomorphic off the zero set of `g` is holomorphic on `U`.
- `subset_closure_diff_zero`: the complement of the zero set of `g` is dense in `U`.
- `interior_inter_preimage_zero_prod_eq_empty`: a finite product of functions whose zero sets
  have empty interior has a zero set with empty interior.
- `IsPreconnected.diff_zero`, `IsConnected.diff_zero`, `IsPreconnected.diff_biUnion_zero`: if `U`
  is connected, so is the complement in `U` of the zero set of `g`, or of finitely many such
  zero sets.
- `AnalyticOnNhd.interior_inter_preimage_zero_eq_empty`: on a connected open set, the zero set of
  an analytic function which is not identically zero has empty interior.

## Proof

Fix `a ∈ U`. There is a direction `v` such that `t ↦ g (a + t • v)` is not identically zero near
`0`, hence it has no zeros on a small circle `‖t‖ = r`, and by compactness neither does
`t ↦ g (z + t • v)` for `z` near `a`. The circle integral
`(2πi)⁻¹ ∮_{‖t‖ = r} t⁻¹ • f (z + t • v)` is holomorphic in `z`, and by the one-variable
removable singularity theorem and Cauchy's formula it equals `f z` whenever `g z ≠ 0`.
-/

open Set Filter Metric Complex
open scoped Topology

section CircleIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- **Holomorphy of parametric circle integrals.** If `G : E → ℂ → ℂ` is jointly continuous on
`U × sphere 0 r` and holomorphic on `U` in the first variable, then `x ↦ ∮ ζ in C(0, r), G x ζ`
is holomorphic on `U`. -/
theorem differentiableOn_circleIntegral {U : Set E} (hU : IsOpen U) {r : ℝ} (hr : 0 < r)
    {G : E → ℂ → ℂ} (hdiff : ∀ ζ ∈ sphere (0 : ℂ) r, DifferentiableOn ℂ (G · ζ) U)
    (hcont : ContinuousOn (Function.uncurry G) (U ×ˢ sphere (0 : ℂ) r)) :
    DifferentiableOn ℂ (fun x ↦ ∮ ζ in C(0, r), G x ζ) U := by
  intro x₀ hx₀
  refine (analyticAt_of_complexChart ?_).differentiableAt.differentiableWithinAt
  obtain ⟨ρ, hρ, hsub⟩ := exists_complexChart_polydisc_subset hU hx₀
  exact analyticAt_circleIntegral (G := fun y ζ ↦ G (x₀ + complexChart E y) ζ) hr hρ
    (fun ζ hζ ↦ (hdiff ζ (by simpa using hζ)).comp
      (by fun_prop : Differentiable ℂ _).differentiableOn fun y hy ↦ hsub y hy)
    (hcont.comp_continuous (f := fun p : (Set.univ.pi fun _ : Fin (Module.finrank ℂ E) ↦
        closedBall (0 : ℂ) ρ) × ℝ ↦
        (x₀ + complexChart E (p.1 : Fin (Module.finrank ℂ E) → ℂ), circleMap 0 r p.2))
      (by fun_prop) fun p ↦ ⟨hsub _ p.1.2, by simp [hr.le]⟩)

end CircleIntegral

section OneVariable

/-- **Riemann extension theorem in one variable**: a holomorphic function off a set `S` of
isolated points in an open set `D ⊆ ℂ`, bounded near every point of `D`, extends to a holomorphic
function on `D`. -/
theorem exists_differentiableOn_eqOn_of_isolated {D S : Set ℂ} (hD : IsOpen D)
    (hS : ∀ p ∈ D, ∀ᶠ t in 𝓝[≠] p, t ∉ S) {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (D \ S))
    (hb : ∀ p ∈ D, IsBoundedUnder (· ≤ ·) (𝓝[≠] p) (fun t ↦ ‖h t‖)) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H D ∧ EqOn H h (D \ S) := by
  -- Near each `p ∈ D`, the only possible point of `S` is `p` itself.
  have hloc : ∀ p ∈ D, ∀ᶠ t in 𝓝 p, t ∈ D ∧ (t ≠ p → t ∉ S) := fun p hp ↦
    Filter.Eventually.and (hD.mem_nhds hp) (eventually_nhdsWithin_iff.mp (hS p hp))
  have hdiffAt : ∀ t ∈ D \ S, DifferentiableAt ℂ h t := by
    intro t ht
    have : ∀ᶠ u in 𝓝 t, u ∈ D \ S := by
      filter_upwards [hloc t ht.1] with u hu
      exact ⟨hu.1, fun huS ↦ by
        rcases eq_or_ne u t with rfl | hne
        · exact ht.2 huS
        · exact hu.2 hne huS⟩
    exact hh.differentiableAt this
  have hpunct : ∀ p ∈ D, ∀ᶠ t in 𝓝[≠] p, t ∈ D \ S := fun p hp ↦ by
    filter_upwards [nhdsWithin_le_nhds (hloc p hp), self_mem_nhdsWithin] with t ht htp
    exact ⟨ht.1, ht.2 htp⟩
  have htend : ∀ p ∈ D, Tendsto h (𝓝[≠] p) (𝓝 (limUnder (𝓝[≠] p) h)) := by
    intro p hp
    refine tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under ?_ ?_
    · filter_upwards [hpunct p hp] with t ht using hdiffAt t ht
    · obtain ⟨C, hC⟩ := hb p hp
      refine ⟨C + ‖h p‖, eventually_map.2 ?_⟩
      filter_upwards [eventually_map.1 hC] with t ht using
        (norm_sub_le _ _).trans (by simpa using ht)
  refine ⟨fun t ↦ limUnder (𝓝[≠] t) h, ?_, ?_⟩
  · have heq : EqOn (fun t ↦ limUnder (𝓝[≠] t) h) h (D \ S) := fun t ht ↦
      ((hdiffAt t ht).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq
    intro p hp
    set N := {t | t ∈ D ∧ (t ≠ p → t ∉ S)}
    have hN : interior N ∈ 𝓝 p := interior_mem_nhds.mpr (hloc p hp)
    refine ((differentiableOn_compl_singleton_and_continuousAt_iff hN).mp ⟨?_, ?_⟩
      |>.differentiableAt hN).differentiableWithinAt
    · intro t ht
      have hopen : IsOpen (interior N \ {p}) := isOpen_interior.sdiff isClosed_singleton
      have hmem : ∀ u ∈ interior N \ {p}, u ∈ D \ S := fun u hu ↦
        ⟨(interior_subset hu.1).1, (interior_subset hu.1).2 hu.2⟩
      refine (hdiffAt t (hmem t ht) |>.congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [hopen.mem_nhds ht] with u hu using heq (hmem u hu)
    · rw [← continuousWithinAt_compl_self]
      refine (htend p hp).congr' ?_
      filter_upwards [hpunct p hp] with t ht using (heq ht).symm
  · intro t ht
    exact ((hdiffAt t ht).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq

end OneVariable

section Density

variable {X : Type*} [TopologicalSpace X] {U : Set X} {g : X → ℂ}

/-- If the zero set of `g` in the open set `U` has empty interior, its complement is dense in
`U`. -/
theorem subset_closure_diff_zero (hU : IsOpen U) (hZ : interior (U ∩ g ⁻¹' {0}) = ∅) :
    U ⊆ closure (U \ g ⁻¹' {0}) := by
  intro z hz
  rw [mem_closure_iff_nhds]
  intro t ht
  by_contra hne
  have hsub : t ∩ U ⊆ U ∩ g ⁻¹' {0} := fun w hw ↦
    ⟨hw.2, by_contra fun hgw ↦ hne ⟨w, hw.1, hw.2, hgw⟩⟩
  have : z ∈ interior (U ∩ g ⁻¹' {0}) :=
    mem_interior_iff_mem_nhds.mpr (mem_of_superset (inter_mem ht (hU.mem_nhds hz)) hsub)
  simp [hZ] at this

/-- Two functions continuous on the open set `U` which agree off the zero set of `g` agree on
`U`, provided this zero set has empty interior. -/
theorem Set.EqOn.of_eqOn_diff_zero {Y : Type*} [TopologicalSpace Y] [T2Space Y] {F₁ F₂ : X → Y}
    (hU : IsOpen U) (hZ : interior (U ∩ g ⁻¹' {0}) = ∅) (h₁ : ContinuousOn F₁ U)
    (h₂ : ContinuousOn F₂ U) (h : EqOn F₁ F₂ (U \ g ⁻¹' {0})) : EqOn F₁ F₂ U :=
  h.of_subset_closure h₁ h₂ sdiff_subset (subset_closure_diff_zero hU hZ)

/-- If the zero sets of `g₁` and `g₂` in `U` have empty interior and `g₁` is
continuous on `U`, then the zero set of `g₁ * g₂` in `U` has empty interior. -/
theorem interior_inter_preimage_zero_mul_eq_empty {g₁ g₂ : X → ℂ}
    (hg₁ : ContinuousOn g₁ U) (h₁ : interior (U ∩ g₁ ⁻¹' {0}) = ∅)
    (h₂ : interior (U ∩ g₂ ⁻¹' {0}) = ∅) : interior (U ∩ (g₁ * g₂) ⁻¹' {0}) = ∅ := by
  set N := interior (U ∩ (g₁ * g₂) ⁻¹' {0})
  have hNU : N ⊆ U := interior_subset.trans inter_subset_left
  have hO : IsOpen (N ∩ g₁ ⁻¹' {0}ᶜ) :=
    (hg₁.mono hNU).isOpen_inter_preimage isOpen_interior isOpen_compl_singleton
  have hO₂ : N ∩ g₁ ⁻¹' {0}ᶜ ⊆ interior (U ∩ g₂ ⁻¹' {0}) := by
    refine interior_maximal (fun w hw ↦ ⟨hNU hw.1, ?_⟩) hO
    have := (interior_subset hw.1).2
    simp only [mem_preimage, Pi.mul_apply, mem_singleton_iff, mul_eq_zero] at this
    exact this.resolve_left hw.2
  rw [h₂, subset_empty_iff] at hO₂
  refine subset_empty_iff.mp (h₁ ▸ interior_maximal (fun w hw ↦ ⟨hNU hw, ?_⟩) isOpen_interior)
  by_contra hg
  exact (eq_empty_iff_forall_notMem.mp hO₂) w ⟨hw, hg⟩

/-- If the zero sets of finitely many functions `g i`, continuous on `U`, have empty
interior in `U`, then so has the zero set of their product. -/
theorem interior_inter_preimage_zero_prod_eq_empty {ι : Type*} (s : Finset ι) {g : ι → X → ℂ}
    (hg : ∀ i ∈ s, ContinuousOn (g i) U)
    (hZ : ∀ i ∈ s, interior (U ∩ g i ⁻¹' {0}) = ∅) :
    interior (U ∩ (fun z ↦ ∏ i ∈ s, g i z) ⁻¹' {0}) = ∅ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp_rw [Finset.prod_insert ha]
    exact interior_inter_preimage_zero_mul_eq_empty (g₁ := g a)
      (hg a (Finset.mem_insert_self a s)) (hZ a (Finset.mem_insert_self a s))
      (ih (fun i hi ↦ hg i (Finset.mem_insert_of_mem hi))
        fun i hi ↦ hZ i (Finset.mem_insert_of_mem hi))

end Density

section SeveralVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E} {g : E → ℂ}

/-- If `U` is preconnected and `g` is analytic on `U` and not identically zero, the zero set of `g`
in `U` has empty interior. -/
theorem AnalyticOnNhd.interior_inter_preimage_zero_eq_empty (hg : AnalyticOnNhd ℂ g U)
    (hU : IsPreconnected U) {z : E} (hz : z ∈ U) (hgz : g z ≠ 0) :
    interior (U ∩ g ⁻¹' {0}) = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr fun z₀ hz₀ ↦ hgz ?_
  have h₀ : g =ᶠ[𝓝 z₀] 0 := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hz₀] with w hw using hw.2
  exact hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU (interior_subset hz₀).1 h₀ hz

/-- There is a direction along which `g` does not vanish identically near `a`. -/
private lemma exists_frequently_ne_zero (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hZ : interior (U ∩ g ⁻¹' {0}) = ∅) {a : E} (ha : a ∈ U) :
    ∃ v : E, ∃ᶠ t in 𝓝 (0 : ℂ), g (a + t • v) ≠ 0 := by
  by_contra! H
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hU a ha
  suffices hsub : ball a ρ ⊆ U ∩ g ⁻¹' {0} by
    have := interior_maximal hsub isOpen_ball (mem_ball_self hρ)
    simp [hZ] at this
  intro z hz
  refine ⟨hball hz, ?_⟩
  set D := (fun t : ℂ ↦ a + t • (z - a)) ⁻¹' ball a ρ
  have hDo : IsOpen D := isOpen_ball.preimage (by fun_prop)
  have hDc : Convex ℝ D := by
    intro t₁ h₁ t₂ h₂ α β hα hβ hαβ
    have := convex_ball a ρ h₁ h₂ hα hβ hαβ
    simp only [D, mem_preimage] at this ⊢
    convert this using 1
    simp only [add_smul, smul_assoc]
    linear_combination (norm := module) -(hαβ • a)
  have hφ : AnalyticOnNhd ℂ (fun t : ℂ ↦ g (a + t • (z - a))) D :=
    (hg.comp (by fun_prop : Differentiable ℂ fun t : ℂ ↦ a + t • (z - a)).differentiableOn
      fun t ht ↦ hball ht).analyticOnNhd hDo
  have h0 : (0 : ℂ) ∈ D := by simp [D, hρ]
  have h1 : (1 : ℂ) ∈ D := by simpa [D] using hz
  have := hφ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hDc.isPreconnected h0
    (H (z - a)) h1
  simpa using this

variable [FiniteDimensional ℂ E]

/-- The local construction behind the Riemann extension theorem: near every point of `U` there is
a holomorphic function which agrees with `f` off the zero set of `g`. -/
private lemma exists_local_extension (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hZ : interior (U ∩ g ⁻¹' {0}) = ∅) {f : E → ℂ}
    (hf : DifferentiableOn ℂ f (U \ g ⁻¹' {0}))
    (hbdd : ∀ z ∈ U, IsBoundedUnder (· ≤ ·) (𝓝[U \ g ⁻¹' {0}] z) (fun w ↦ ‖f w‖))
    {a : E} (ha : a ∈ U) :
    ∃ δ > 0, ∃ F : E → ℂ, ball a δ ⊆ U ∧ DifferentiableOn ℂ F (ball a δ) ∧
      ∀ z ∈ ball a δ, g z ≠ 0 → F z = f z := by
  obtain ⟨v, hv⟩ := exists_frequently_ne_zero hU hg hZ ha
  set W := U \ g ⁻¹' {0}
  have hW : IsOpen W := hg.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
  set ψ : ℂ → E := fun t ↦ a + t • v
  have hψ : Continuous ψ := by fun_prop
  have hφ : AnalyticAt ℂ (fun t ↦ g (ψ t)) 0 :=
    (hg.comp (by fun_prop : Differentiable ℂ ψ).differentiableOn fun t ht ↦ ht).analyticAt
      ((hψ.continuousAt (x := 0)).preimage_mem_nhds
        (show U ∈ 𝓝 (ψ 0) by simpa [ψ] using hU.mem_nhds ha))
  have hne : ∀ᶠ t in 𝓝[≠] (0 : ℂ), g (ψ t) ≠ 0 := by
    refine hφ.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun h ↦ ?_
    obtain ⟨t, h1, h2⟩ := (hv.and_eventually h).exists
    exact h1 h2
  have hev : ∀ᶠ t in 𝓝 (0 : ℂ), ψ t ∈ U ∧ (t ≠ 0 → g (ψ t) ≠ 0) :=
    Filter.Eventually.and ((hψ.continuousAt (x := 0)).preimage_mem_nhds
        (show U ∈ 𝓝 (ψ 0) by simpa [ψ] using hU.mem_nhds ha))
      (eventually_nhdsWithin_iff.mp hne)
  obtain ⟨r₀, hr₀, hr₀U⟩ := Metric.eventually_nhds_iff_ball.mp hev
  set r := r₀ / 3
  set r' := 2 * r₀ / 3
  have hr : 0 < r := by positivity
  have hrr' : r < r' := by simp only [r, r']; linarith
  have hr'r₀ : r' < r₀ := by simp only [r']; linarith
  have hCW : ψ '' sphere 0 r ⊆ W := by
    rintro _ ⟨t, ht, rfl⟩
    have ht' : ‖t‖ = r := by simpa using ht
    have := hr₀U t (by simp [ht']; linarith)
    exact ⟨this.1, this.2 (by rintro rfl; simp at ht'; linarith)⟩
  have hKU : ψ '' closedBall 0 r' ⊆ U := by
    rintro _ ⟨t, ht, rfl⟩
    exact (hr₀U t (closedBall_subset_ball hr'r₀ ht)).1
  obtain ⟨δ₁, hδ₁, hδ₁W⟩ := ((isCompact_sphere 0 r).image hψ).exists_thickening_subset_open hW hCW
  obtain ⟨δ₂, hδ₂, hδ₂U⟩ :=
    ((isCompact_closedBall 0 r').image hψ).exists_thickening_subset_open hU hKU
  set δ := min δ₁ δ₂
  have hdist : ∀ z ∈ ball a δ, ∀ t : ℂ, dist (z + t • v) (ψ t) < δ := by
    intro z hz t
    simpa [ψ, dist_eq_norm, add_sub_add_right_eq_sub] using hz
  have hcirc : ∀ z ∈ ball a δ, ∀ t ∈ sphere (0 : ℂ) r, z + t • v ∈ W := fun z hz t ht ↦
    hδ₁W (mem_thickening_iff.mpr
      ⟨ψ t, mem_image_of_mem _ ht, (hdist z hz t).trans_le (min_le_left _ _)⟩)
  have hdisc : ∀ z ∈ ball a δ, ∀ t ∈ closedBall (0 : ℂ) r', z + t • v ∈ U := fun z hz t ht ↦
    hδ₂U (mem_thickening_iff.mpr
      ⟨ψ t, mem_image_of_mem _ ht, (hdist z hz t).trans_le (min_le_right _ _)⟩)
  have hballU : ball a δ ⊆ U := fun z hz ↦ by
    simpa using hdisc z hz 0 (mem_closedBall_self (by positivity))
  refine ⟨δ, lt_min hδ₁ hδ₂, fun z ↦ (2 * Real.pi * I)⁻¹ • ∮ t in C(0, r), t⁻¹ • f (z + t • v),
    hballU, ?_, ?_⟩
  · refine (differentiableOn_circleIntegral isOpen_ball hr (fun ζ hζ ↦ ?_) ?_).const_smul
      ((2 * Real.pi * I)⁻¹ : ℂ)
    · exact (hf.comp (differentiableOn_id.add_const _) fun z hz ↦ hcirc z hz ζ hζ).const_smul ζ⁻¹
    · refine ContinuousOn.smul (continuousOn_snd.inv₀ fun p hp ↦ ?_)
        (hf.continuousOn.comp (by fun_prop) fun p hp ↦ hcirc p.1 hp.1 p.2 hp.2)
      have := hp.2
      rintro h
      simp [h] at this
      linarith
  · intro z hz hgz
    set D := ball (0 : ℂ) r'
    set S := {t : ℂ | g (z + t • v) = 0}
    have hDU : ∀ t ∈ D, z + t • v ∈ U := fun t ht ↦ hdisc z hz t (ball_subset_closedBall ht)
    have hγ : AnalyticOnNhd ℂ (fun t : ℂ ↦ g (z + t • v)) D :=
      (hg.comp (by fun_prop : Differentiable ℂ fun t : ℂ ↦ z + t • v).differentiableOn
        hDU).analyticOnNhd isOpen_ball
    have hrS : (r : ℂ) ∉ S := (hcirc z hz r (by simp [hr.le])).2
    have hrD : (r : ℂ) ∈ D := by simpa [D, abs_of_pos hr] using hrr'
    have hS : ∀ p ∈ D, ∀ᶠ t in 𝓝[≠] p, t ∉ S := by
      intro p hp
      by_contra h
      rw [not_eventually] at h
      exact hrS (hγ.eqOn_zero_of_preconnected_of_frequently_eq_zero
        (convex_ball 0 r').isPreconnected hp (by simpa [S] using h) hrD)
    have hDS : ∀ t ∈ D \ S, z + t • v ∈ W := fun t ht ↦ ⟨hDU t ht.1, ht.2⟩
    obtain ⟨H, hHd, hHeq⟩ := exists_differentiableOn_eqOn_of_isolated isOpen_ball hS
      (h := fun t ↦ f (z + t • v))
      (hf.comp (by fun_prop : Differentiable ℂ fun t : ℂ ↦ z + t • v).differentiableOn hDS)
      (fun p hp ↦ by
        refine Tendsto.isBoundedUnder_comp (f := fun w ↦ ‖f w‖)
          (tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩) (hbdd _ (hDU p hp))
        · exact ((by fun_prop : Continuous fun t : ℂ ↦ z + t • v).tendsto p).mono_left
            nhdsWithin_le_nhds
        · filter_upwards [nhdsWithin_le_nhds (isOpen_ball.mem_nhds hp), hS p hp] with t h1 h2
          exact hDS t ⟨h1, h2⟩)
    have hsub : closedBall (0 : ℂ) r ⊆ D := closedBall_subset_ball hrr'
    have h0 : (0 : ℂ) ∈ D \ S := ⟨mem_ball_self (by positivity), by simpa [S] using hgz⟩
    have hC := (hHd.mono hsub).circleIntegral_sub_inv_smul (mem_ball_self hr)
    have hcongr : (∮ t in C(0, r), (t - 0)⁻¹ • H t) = ∮ t in C(0, r), t⁻¹ • f (z + t • v) := by
      refine circleIntegral.integral_congr hr.le fun t ht ↦ ?_
      simp only [sub_zero]
      rw [hHeq ⟨hsub (sphere_subset_closedBall ht), (hcirc z hz t ht).2⟩]
    rw [hcongr, hHeq h0] at hC
    simp only [hC, zero_smul, add_zero]
    exact inv_smul_smul₀ two_pi_I_ne_zero _

/-- **Riemann extension theorem.** Let `U` be an open subset of a finite-dimensional complex space
and `g` holomorphic on `U` whose zero set in `U` has empty interior. A function holomorphic on
`U \ g ⁻¹' {0}` and bounded near every point of `U` extends to a holomorphic function on `U`. -/
theorem exists_differentiableOn_eqOn_of_isBoundedUnder (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) (hZ : interior (U ∩ g ⁻¹' {0}) = ∅) {f : E → ℂ}
    (hf : DifferentiableOn ℂ f (U \ g ⁻¹' {0}))
    (hbdd : ∀ z ∈ U, IsBoundedUnder (· ≤ ·) (𝓝[U \ g ⁻¹' {0}] z) (fun w ↦ ‖f w‖)) :
    ∃ F : E → ℂ, DifferentiableOn ℂ F U ∧ EqOn F f (U \ g ⁻¹' {0}) := by
  set W := U \ g ⁻¹' {0}
  have hdense := subset_closure_diff_zero hU hZ
  -- The extension is the limit of `f` along `W`; it agrees with every local extension.
  have hloc : ∀ a ∈ U, ∃ δ > 0, ∃ F : E → ℂ, DifferentiableOn ℂ F (ball a δ) ∧
      ∀ z ∈ ball a δ, limUnder (𝓝[W] z) f = F z := by
    intro a ha
    obtain ⟨δ, hδ, F, hFU, hFd, hFf⟩ := exists_local_extension hU hg hZ hf hbdd ha
    refine ⟨δ, hδ, F, hFd, fun z hz ↦ ?_⟩
    have : (𝓝[W] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hdense (hFU hz))
    refine Tendsto.limUnder_eq ?_
    refine ((hFd.differentiableAt (isOpen_ball.mem_nhds hz)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds).congr' ?_
    filter_upwards [nhdsWithin_le_nhds (isOpen_ball.mem_nhds hz), self_mem_nhdsWithin]
      with w hw hwW using hFf w hw hwW.2
  refine ⟨fun z ↦ limUnder (𝓝[W] z) f, fun a ha ↦ ?_, fun z hz ↦ ?_⟩
  · obtain ⟨δ, hδ, F, hFd, hF⟩ := hloc a ha
    refine ((hFd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hδ))).congr_of_eventuallyEq
      ?_).differentiableWithinAt
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hδ)] with z hz using hF z hz
  · have hW : IsOpen W := hg.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
    have : (𝓝[W] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (subset_closure hz)
    exact ((hf.differentiableAt (hW.mem_nhds hz)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds).limUnder_eq

/-- A function continuous on `U` and holomorphic off the zero set of `g` is holomorphic on `U`,
provided `g` is holomorphic on `U` and its zero set in `U` has empty interior. -/
theorem DifferentiableOn.of_continuousOn_of_differentiableOn_diff_zero (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) (hZ : interior (U ∩ g ⁻¹' {0}) = ∅) {f : E → ℂ}
    (hfc : ContinuousOn f U) (hf : DifferentiableOn ℂ f (U \ g ⁻¹' {0})) :
    DifferentiableOn ℂ f U := by
  obtain ⟨F, hFd, hFf⟩ := exists_differentiableOn_eqOn_of_isBoundedUnder hU hg hZ hf
    fun z hz ↦ (((hfc.continuousAt (hU.mem_nhds hz)).norm.tendsto.isBoundedUnder_le).mono
      nhdsWithin_le_nhds)
  exact hFd.congr (EqOn.of_eqOn_diff_zero hU hZ hfc hFd.continuousOn hFf.symm)

/-- If `U` is open and preconnected, `g` is holomorphic on `U` and the zero set of `g` in `U` has
empty interior, then its complement `U \ g ⁻¹' {0}` is preconnected. -/
theorem IsPreconnected.diff_zero (hU : IsOpen U) (hUc : IsPreconnected U)
    (hg : DifferentiableOn ℂ g U) (hZ : interior (U ∩ g ⁻¹' {0}) = ∅) :
    IsPreconnected (U \ g ⁻¹' {0}) := by
  classical
  set W := U \ g ⁻¹' {0}
  have hW : IsOpen W := hg.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hWuv hWd
  have hdisj : ∀ w ∈ W, w ∈ v → w ∉ u := fun w hw hwv hwu ↦
    (eq_empty_iff_forall_notMem.mp hWd) w ⟨hw, hwu, hwv⟩
  set χ : E → ℂ := fun z ↦ if z ∈ u then 1 else 0
  have hχ : DifferentiableOn ℂ χ W := by
    intro w hw
    refine DifferentiableAt.differentiableWithinAt ?_
    by_cases hwu : w ∈ u
    · refine (differentiableAt_const (1 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [hu.mem_nhds hwu] with z hz using ite_eq_left hz
    · have hwv : w ∈ v := (hWuv hw).resolve_left hwu
      refine (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [hv.mem_nhds hwv, hW.mem_nhds hw] with z hzv hzW
      exact ite_eq_right (hdisj z hzW hzv)
  have hχb : ∀ z, ‖χ z‖ ≤ 1 := fun z ↦ by by_cases hz : z ∈ u <;> simp [χ, hz]
  obtain ⟨X, hXd, hXχ⟩ := exists_differentiableOn_eqOn_of_isBoundedUnder hU hg hZ hχ
    fun _ _ ↦ isBoundedUnder_of ⟨1, hχb⟩
  have hXc := hXd.continuousOn
  have h01 : ∀ z ∈ U, X z = 0 ∨ X z = 1 := by
    intro z hz
    have hmem := ((hXc z hz).mono sdiff_subset).mem_closure_image
      (subset_closure_diff_zero hU hZ hz)
    have hsub : X '' W ⊆ {0, 1} := by
      rintro _ ⟨w, hw, rfl⟩
      rw [hXχ hw]
      by_cases hwu : w ∈ u <;> simp [χ, hwu]
    have := closure_minimal hsub (Set.toFinite _).isClosed hmem
    simpa [or_comm] using this
  have hA := hXc.isOpen_inter_preimage hU (isOpen_ball (x := (1 : ℂ)) (ε := 1 / 2))
  have hB := hXc.isOpen_inter_preimage hU (isOpen_ball (x := (0 : ℂ)) (ε := 1 / 2))
  have hUAB : U ⊆ (U ∩ X ⁻¹' ball 1 (1 / 2)) ∪ (U ∩ X ⁻¹' ball 0 (1 / 2)) := by
    intro z hz
    rcases h01 z hz with h | h
    · exact Or.inr ⟨hz, by simp [h]⟩
    · exact Or.inl ⟨hz, by simp [h]⟩
  have hABd : U ∩ ((U ∩ X ⁻¹' ball 1 (1 / 2)) ∩ (U ∩ X ⁻¹' ball 0 (1 / 2))) = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr fun z hz ↦ ?_
    have h1 : ‖X z - 1‖ < 1 / 2 := by simpa [dist_eq_norm] using hz.2.1.2
    have h0 : ‖X z‖ < 1 / 2 := by simpa using hz.2.2.2
    have := norm_sub_le (X z) (X z - 1)
    simp only [sub_sub_cancel, norm_one] at this
    linarith
  rcases (isPreconnected_iff_subset_of_disjoint.mp hUc) _ _ hA hB hUAB hABd with h | h
  · refine Or.inl fun w hw ↦ by_contra fun hwu ↦ ?_
    have := (h hw.1).2
    simp [hXχ hw, χ, hwu] at this
    norm_num at this
  · refine Or.inr fun w hw ↦ (hWuv hw).resolve_left fun hwu ↦ ?_
    have := (h hw.1).2
    simp [hXχ hw, χ, hwu] at this
    norm_num at this

/-- If `U` is open and connected, `g` is holomorphic on `U` and the zero set of `g` in `U` has
empty interior, then its complement `U \ g ⁻¹' {0}` is connected. -/
theorem IsConnected.diff_zero (hU : IsOpen U) (hUc : IsConnected U)
    (hg : DifferentiableOn ℂ g U) (hZ : interior (U ∩ g ⁻¹' {0}) = ∅) :
    IsConnected (U \ g ⁻¹' {0}) := by
  refine ⟨?_, hUc.isPreconnected.diff_zero hU hg hZ⟩
  obtain ⟨z, hz⟩ := hUc.nonempty
  exact closure_nonempty_iff.mp ⟨z, subset_closure_diff_zero hU hZ hz⟩

/-- If `U` is open and preconnected and `g i`, `i ∈ s`, are finitely many functions holomorphic on
`U` whose zero sets in `U` have empty interior, then `U` minus the union of these zero sets is
preconnected. -/
theorem IsPreconnected.diff_biUnion_zero {ι : Type*} (s : Finset ι) {g : ι → E → ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hg : ∀ i ∈ s, DifferentiableOn ℂ (g i) U)
    (hZ : ∀ i ∈ s, interior (U ∩ g i ⁻¹' {0}) = ∅) :
    IsPreconnected (U \ ⋃ i ∈ s, g i ⁻¹' {0}) := by
  have hprod : DifferentiableOn ℂ (fun z ↦ ∏ i ∈ s, g i z) U := by
    classical
    clear hZ
    induction s using Finset.induction_on with
    | empty => simp [differentiableOn_const]
    | insert a s ha ih =>
      simp_rw [Finset.prod_insert ha]
      exact (hg a (Finset.mem_insert_self a s)).mul
        (ih fun i hi ↦ hg i (Finset.mem_insert_of_mem hi))
  have heq : (⋃ i ∈ s, g i ⁻¹' {0}) = (fun z ↦ ∏ i ∈ s, g i z) ⁻¹' {0} := by
    ext z
    simp [Finset.prod_eq_zero_iff]
  rw [heq]
  exact hUc.diff_zero hU hprod
    (interior_inter_preimage_zero_prod_eq_empty s (fun i hi ↦ (hg i hi).continuousOn) hZ)

end SeveralVariables
