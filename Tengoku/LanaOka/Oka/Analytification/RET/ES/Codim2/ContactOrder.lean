/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.Seed.Analysis.Analytic.Order
import Tengoku.Seed.Analysis.Complex.AbsMax
import Tengoku.Seed.Analysis.Complex.Schwarz
import Tengoku.LanaOka.Oka.Analytic.RiemannExtension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Contact orders of branches which are disjoint off `t = 0`

Let `E` be a complex normed space and let `δ` be holomorphic on an open `V ⊆ E × ℂ`, with
coordinates `(y, t)`, such that `δ(y, t) ≠ 0` whenever `t ≠ 0`. This is the difference of two
branches `w = ψᵢ(y, t)` and `w = ψⱼ(y, t)` of a hypersurface whose branches are disjoint over
`t ≠ 0`, as produced by Puiseux expansions (`Puiseux.exists_prod_eq`).

The zeros of `δ(·, 0)` form an open set (`Codim2.eventually_apply_zero_eq_zero`): by the maximum
modulus principle for `1 / δ(y, ·)`, `‖δ(y, 0)‖` is at least the minimum of `‖δ(y, ·)‖` on a small
circle, and this minimum stays away from `0` for `y` near a point `y₀`. Hence over a preconnected
open `G`, `δ(·, 0)` vanishes identically or nowhere (`Codim2.apply_zero_eq_zero_or_ne_zero`), and
on `G × Δ_r` we have `δ = tᵏ u` with `u` holomorphic and nowhere zero (`Codim2.exists_eq_pow_mul`):
the two branches have contact order `k` along `t = 0`.

## Main results

- `Codim2.eventually_apply_zero_eq_zero`: the zeros of `δ(·, 0)` form an open set.
- `Codim2.apply_zero_eq_zero_or_ne_zero`: `δ(·, 0)` vanishes identically or nowhere.
- `Codim2.exists_eq_mul_of_apply_zero`: a holomorphic function vanishing on `t = 0` is `t` times
  a holomorphic function.
- `Codim2.exists_eq_pow_mul`: `δ = tᵏ u` with `u` holomorphic and nowhere zero.
-/

open Set Filter Metric Topology

namespace Codim2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Let `δ` be holomorphic on an open `V ⊆ E × ℂ` without zeros off `t = 0`. If `δ(y₀, 0) = 0`,
then `δ(y, 0) = 0` for all `y` near `y₀`. -/
theorem eventually_apply_zero_eq_zero {V : Set (E × ℂ)} (hV : IsOpen V) {δ : E × ℂ → ℂ}
    (hδ : DifferentiableOn ℂ δ V) (hne : ∀ z ∈ V, z.2 ≠ 0 → δ z ≠ 0) {y₀ : E}
    (hy₀ : (y₀, 0) ∈ V) (h0 : δ (y₀, 0) = 0) : ∀ᶠ y in 𝓝 y₀, δ (y, 0) = 0 := by
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.1 hV _ hy₀
  rw [← ball_prod_same] at hεV
  set ρ := ε / 2
  have hρ0 : 0 < ρ := half_pos hε
  have hmem {y : E} (hy : y ∈ ball y₀ ε) {t : ℂ} (ht : ‖t‖ ≤ ρ) : (y, t) ∈ V :=
    hεV ⟨hy, mem_ball_zero_iff.2 (ht.trans_lt (half_lt_self hε))⟩
  have hK : IsCompact (sphere (0 : ℂ) ρ) := isCompact_sphere 0 ρ
  have hcont : ContinuousOn (fun t : ℂ ↦ ‖δ (y₀, t)‖) (sphere 0 ρ) :=
    (hδ.continuousOn.comp (by fun_prop : Continuous fun t : ℂ ↦ (y₀, t)).continuousOn
      fun t ht ↦ hmem (mem_ball_self hε) (mem_sphere_zero_iff_norm.1 ht).le).norm
  obtain ⟨t₁, ht₁, hmin⟩ :=
    hK.exists_isMinOn (NormedSpace.sphere_nonempty.2 hρ0.le) hcont
  set c := ‖δ (y₀, t₁)‖
  have hc : 0 < c := norm_pos_iff.2 (hne _ (hmem (mem_ball_self hε)
    (mem_sphere_zero_iff_norm.1 ht₁).le) (by
      rintro rfl
      rw [mem_sphere_zero_iff_norm, norm_zero] at ht₁
      exact hρ0.ne ht₁))
  have hcirc : ∀ᶠ y in 𝓝 y₀, ∀ t ∈ sphere (0 : ℂ) ρ, c / 2 < ‖δ (y, t)‖ := by
    refine hK.eventually_forall_of_forall_eventually fun t ht ↦ ?_
    have hVt : (y₀, t) ∈ V := hmem (mem_ball_self hε) (mem_sphere_zero_iff_norm.1 ht).le
    exact (hδ.continuousOn.continuousAt (hV.mem_nhds hVt)).norm.eventually
      (lt_mem_nhds ((half_lt_self hc).trans_le (isMinOn_iff.1 hmin t ht)))
  have hcen : ∀ᶠ y in 𝓝 y₀, ‖δ (y, 0)‖ < c / 2 := by
    have h1 : ContinuousAt (fun y ↦ δ (y, 0)) y₀ :=
      (hδ.continuousOn.continuousAt (hV.mem_nhds hy₀)).comp (x := y₀) (by fun_prop)
    refine h1.norm.eventually (gt_mem_nhds ?_)
    change ‖δ (y₀, 0)‖ < c / 2
    rw [h0, norm_zero]
    exact half_pos hc
  filter_upwards [hcirc, hcen, ball_mem_nhds y₀ hε] with y hy hy0 hyε
  by_contra hne0
  have hd : DiffContOnCl ℂ (fun t : ℂ ↦ (δ (y, t))⁻¹) (ball 0 ρ) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ hρ0.ne']
    refine (hδ.comp (by fun_prop) fun t ht ↦ hmem hyε (mem_closedBall_zero_iff.1 ht)).inv
      fun t ht ↦ ?_
    by_cases ht0 : t = 0
    · rw [ht0]
      exact hne0
    · exact hne _ (hmem hyε (mem_closedBall_zero_iff.1 ht)) ht0
  have hle := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd (C := 2 / c)
    (fun t ht ↦ ?_) (subset_closure (mem_ball_self hρ0))
  · rw [norm_inv] at hle
    have := inv_strictAnti₀ (norm_pos_iff.2 hne0) hy0
    rw [inv_div] at this
    linarith
  · rw [frontier_ball _ hρ0.ne'] at ht
    rw [norm_inv, ← inv_div]
    exact inv_anti₀ (half_pos hc) (hy t ht).le

/-- Let `δ` be holomorphic on an open `V ⊆ E × ℂ` without zeros off `t = 0`, and let `G` be a
preconnected open with `G × {0} ⊆ V`. Then `δ(·, 0)` vanishes identically or nowhere on `G`. -/
theorem apply_zero_eq_zero_or_ne_zero {G : Set E} (hGo : IsOpen G) (hG : IsPreconnected G)
    {V : Set (E × ℂ)} (hV : IsOpen V) (hGV : ∀ y ∈ G, (y, 0) ∈ V) {δ : E × ℂ → ℂ}
    (hδ : DifferentiableOn ℂ δ V) (hne : ∀ z ∈ V, z.2 ≠ 0 → δ z ≠ 0) :
    (∀ y ∈ G, δ (y, 0) = 0) ∨ ∀ y ∈ G, δ (y, 0) ≠ 0 := by
  by_cases h : ∃ y ∈ G, δ (y, 0) = 0
  swap
  · simp only [not_exists, not_and] at h
    exact Or.inr h
  left
  obtain ⟨y₁, hy₁, h₁⟩ := h
  have hc : ContinuousOn (fun y ↦ δ (y, 0)) G :=
    hδ.continuousOn.comp (by fun_prop : Continuous fun y : E ↦ (y, (0 : ℂ))).continuousOn
      fun y hy ↦ hGV y hy
  have hev (y : E) (hy : y ∈ G) (h0 : δ (y, 0) = 0) : ∀ᶠ y' in 𝓝 y, δ (y', 0) = 0 :=
    eventually_apply_zero_eq_zero hV hδ hne (hGV y hy) h0
  have hsub : G ⊆ {y | ∀ᶠ y' in 𝓝 y, δ (y', 0) = 0} ∪ G ∩ (fun y ↦ δ (y, 0)) ⁻¹' {0}ᶜ :=
    fun y hy ↦ by
      by_cases h0 : δ (y, 0) = 0
      · exact Or.inl (hev y hy h0)
      · exact Or.inr ⟨hy, h0⟩
  have hGu := hG.subset_left_of_subset_union isOpen_setOfPred_eventually_nhds
    (hc.isOpen_inter_preimage hGo isOpen_compl_singleton)
    (Set.disjoint_left.2 fun y hyu hyv ↦
      hyv.2 (show ∀ᶠ y' in 𝓝 y, δ (y', 0) = 0 from hyu).self_of_nhds) hsub
    ⟨y₁, hy₁, hev y₁ hy₁ h₁⟩
  exact fun y hy ↦ (show ∀ᶠ y' in 𝓝 y, δ (y', 0) = 0 from hGu hy).self_of_nhds

omit [NormedSpace ℂ E] in
/-- The hyperplane `t = 0` has empty interior in any subset of `E × ℂ`. -/
lemma interior_inter_preimage_snd_zero (V : Set (E × ℂ)) :
    interior (V ∩ Prod.snd ⁻¹' {0}) = ∅ := by
  refine eq_empty_of_subset_empty ((interior_mono inter_subset_right).trans ?_)
  rw [← univ_prod, interior_prod_eq, interior_singleton, prod_empty]

variable [FiniteDimensional ℂ E]

/-- A holomorphic function on an open `V ⊆ E × ℂ` which vanishes on `t = 0` is `t` times a
holomorphic function on `V`. -/
theorem exists_eq_mul_of_apply_zero {V : Set (E × ℂ)} (hV : IsOpen V) {δ : E × ℂ → ℂ}
    (hδ : DifferentiableOn ℂ δ V) (h0 : ∀ z ∈ V, z.2 = 0 → δ z = 0) :
    ∃ δ₁ : E × ℂ → ℂ, DifferentiableOn ℂ δ₁ V ∧ ∀ z ∈ V, δ z = z.2 * δ₁ z := by
  set f : E × ℂ → ℂ := fun z ↦ δ z / z.2
  have hf : DifferentiableOn ℂ f (V \ Prod.snd ⁻¹' {0}) :=
    by
      simp only [f, div_eq_mul_inv]
      exact (hδ.mono sdiff_subset).mul (differentiableOn_snd.inv fun z hz ↦ hz.2)
  have hVo : IsOpen (V \ Prod.snd ⁻¹' {0}) :=
    hV.sdiff (isClosed_singleton.preimage continuous_snd)
  suffices hbdd : ∀ z ∈ V, IsBoundedUnder (· ≤ ·) (𝓝[V \ Prod.snd ⁻¹' {0}] z) (‖f ·‖) by
    obtain ⟨F, hF, hFf⟩ := exists_differentiableOn_eqOn_of_isBoundedUnder hV
      differentiableOn_snd (interior_inter_preimage_snd_zero V) hf hbdd
    refine ⟨F, hF, fun z hz ↦ ?_⟩
    by_cases hz0 : z.2 = 0
    · rw [h0 z hz hz0, hz0, zero_mul]
    · rw [hFf ⟨hz, hz0⟩, mul_div_cancel₀ _ hz0]
  intro z hz
  by_cases hz0 : z.2 = 0
  swap
  · exact (hf.differentiableAt (hVo.mem_nhds ⟨hz, hz0⟩)).continuousAt.norm.tendsto
      |>.isBoundedUnder_le.mono nhdsWithin_le_nhds
  -- Near `t = 0`, `‖δ‖ < 1` on a polydisc of radius `ε`, so `‖δ / t‖ ≤ 1 / ε` by Schwarz.
  have hnhds : V ∩ {w | ‖δ w‖ < 1} ∈ 𝓝 z := inter_mem (hV.mem_nhds hz)
    ((hδ.continuousOn.continuousAt (hV.mem_nhds hz)).norm.eventually
      (gt_mem_nhds (show ‖δ z‖ < 1 by rw [h0 z hz hz0, norm_zero]; exact one_pos)))
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hnhds
  refine isBoundedUnder_of_eventually_le (a := 1 / ε) ?_
  filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds z hε), self_mem_nhdsWithin] with w hw hwV
  obtain ⟨y, t⟩ := w
  have hball : ball z ε = ball z.1 ε ×ˢ ball 0 ε := by
    rw [ball_prod_same, ← hz0]
  rw [hball] at hεV hw
  have hin (s : ℂ) (hs : s ∈ ball (0 : ℂ) ε) : (y, s) ∈ V ∧ ‖δ (y, s)‖ < 1 :=
    hεV (show (y, s) ∈ ball z.1 ε ×ˢ ball 0 ε from ⟨hw.1, hs⟩)
  have hy0 : δ (y, 0) = 0 := h0 (y, 0) (hin 0 (mem_ball_self hε)).1 rfl
  have hmaps : MapsTo (fun s : ℂ ↦ δ (y, s)) (ball 0 ε) (closedBall (δ (y, 0)) 1) := by
    intro s hs
    change δ (y, s) ∈ closedBall (δ (y, 0)) 1
    rw [hy0, mem_closedBall_zero_iff]
    exact (hin s hs).2.le
  have hd : DifferentiableOn ℂ (fun s : ℂ ↦ δ (y, s)) (ball 0 ε) :=
    hδ.comp (by fun_prop) fun s hs ↦ (hin s hs).1
  have := Complex.norm_dslope_le_div_of_mapsTo_ball hd hmaps hw.2
  rwa [dslope_of_ne _ hwV.2, slope_def_field, hy0, sub_zero, sub_zero] at this

/-- **Contact order.** Let `G ⊆ E` be open and preconnected and let `δ` be holomorphic on
`G × Δ_r` without zeros off `t = 0`. Then `δ = tᵏ u` for some `k` and some holomorphic `u` without
zeros on `G × Δ_r`. -/
theorem exists_eq_pow_mul {G : Set E} (hGo : IsOpen G) (hG : IsPreconnected G) {r : ℝ}
    {δ : E × ℂ → ℂ} (hδ : DifferentiableOn ℂ δ (G ×ˢ ball 0 r))
    (hne : ∀ z ∈ G ×ˢ ball (0 : ℂ) r, z.2 ≠ 0 → δ z ≠ 0) :
    ∃ (k : ℕ) (u : E × ℂ → ℂ), DifferentiableOn ℂ u (G ×ˢ ball 0 r) ∧
      (∀ z ∈ G ×ˢ ball (0 : ℂ) r, u z ≠ 0) ∧
      ∀ z ∈ G ×ˢ ball (0 : ℂ) r, δ z = z.2 ^ k * u z := by
  set V := G ×ˢ ball (0 : ℂ) r
  have hV : IsOpen V := hGo.prod isOpen_ball
  rcases G.eq_empty_or_nonempty with rfl | ⟨y₀, hy₀⟩
  · exact ⟨0, δ, hδ, by simp [V], by simp [V]⟩
  rcases le_or_gt r 0 with hr | hr
  · have hV0 : V = ∅ := by simp [V, ball_eq_empty.2 hr]
    exact ⟨0, δ, hδ, by simp [hV0], by simp [hV0]⟩
  have hGV : ∀ y ∈ G, (y, 0) ∈ V := fun y hy ↦ ⟨hy, mem_ball_self hr⟩
  have hsl {δ : E × ℂ → ℂ} (hδ : DifferentiableOn ℂ δ V) :
      AnalyticAt ℂ (fun t ↦ δ (y₀, t)) 0 :=
    (hδ.comp (by fun_prop) fun t ht ↦ ⟨hy₀, ht⟩).analyticAt (ball_mem_nhds 0 hr)
  suffices h : ∀ (n : ℕ) (δ : E × ℂ → ℂ), DifferentiableOn ℂ δ V →
      (∀ z ∈ V, z.2 ≠ 0 → δ z ≠ 0) → analyticOrderAt (fun t ↦ δ (y₀, t)) 0 = n →
      ∃ (k : ℕ) (u : E × ℂ → ℂ), DifferentiableOn ℂ u V ∧ (∀ z ∈ V, u z ≠ 0) ∧
        ∀ z ∈ V, δ z = z.2 ^ k * u z by
    refine h _ δ hδ hne (ENat.natCast_toNat fun htop ↦ ?_).symm
    have h1 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), δ (y₀, t) = 0 :=
      (analyticOrderAt_eq_top.1 htop).filter_mono nhdsWithin_le_nhds
    have h2 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ∈ ball (0 : ℂ) r :=
      nhdsWithin_le_nhds (ball_mem_nhds 0 hr)
    have h3 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ≠ 0 := self_mem_nhdsWithin
    obtain ⟨t, ht0, ht1, ht2⟩ := (h3.and (h1.and h2)).exists
    exact hne (y₀, t) ⟨hy₀, ht2⟩ ht0 ht1
  intro n
  induction n with
  | zero =>
    intro δ hδ hne hn
    rw [Nat.cast_zero, analyticOrderAt_eq_zero] at hn
    have h0 : δ (y₀, 0) ≠ 0 := hn.resolve_left (not_not.2 (hsl hδ))
    rcases apply_zero_eq_zero_or_ne_zero hGo hG hV hGV hδ hne with h | h
    · exact absurd (h y₀ hy₀) h0
    refine ⟨0, δ, hδ, fun z hz ↦ ?_, fun z _ ↦ by rw [pow_zero, one_mul]⟩
    by_cases hz0 : z.2 = 0
    · have := h z.1 hz.1
      rwa [show ((z.1, 0) : E × ℂ) = z from Prod.ext rfl hz0.symm] at this
    · exact hne z hz hz0
  | succ n ih =>
    intro δ hδ hne hn
    have h0 : δ (y₀, 0) = 0 :=
      apply_eq_zero_of_analyticOrderAt_ne_zero (f := fun t ↦ δ (y₀, t)) (by rw [hn]; simp)
    rcases apply_zero_eq_zero_or_ne_zero hGo hG hV hGV hδ hne with h | h
    swap
    · exact absurd h0 (h y₀ hy₀)
    obtain ⟨δ₁, hδ₁, hδδ₁⟩ := exists_eq_mul_of_apply_zero hV hδ fun z hz hz0 ↦ by
      have := h z.1 hz.1
      rwa [show ((z.1, 0) : E × ℂ) = z from Prod.ext rfl hz0.symm] at this
    have hne₁ : ∀ z ∈ V, z.2 ≠ 0 → δ₁ z ≠ 0 := fun z hz hz0 h₁ ↦
      hne z hz hz0 (by rw [hδδ₁ z hz, h₁, mul_zero])
    have hord : analyticOrderAt (fun t ↦ δ₁ (y₀, t)) 0 = n := by
      have heq : (fun t ↦ δ (y₀, t)) =ᶠ[𝓝 0] (id : ℂ → ℂ) * fun t ↦ δ₁ (y₀, t) := by
        filter_upwards [ball_mem_nhds (0 : ℂ) hr] with t ht using hδδ₁ _ ⟨hy₀, ht⟩
      rw [analyticOrderAt_congr heq, analyticOrderAt_mul analyticAt_id (hsl hδ₁)] at hn
      have hid : analyticOrderAt (id : ℂ → ℂ) 0 = 1 := by
        exact analyticOrderAt_id
      rw [hid, Nat.cast_succ, add_comm] at hn
      exact WithTop.add_right_cancel ENat.one_ne_top hn
    obtain ⟨k, u, hu, hu0, hδ₁u⟩ := ih δ₁ hδ₁ hne₁ hord
    refine ⟨k + 1, u, hu, hu0, fun z hz ↦ ?_⟩
    rw [hδδ₁ z hz, hδ₁u z hz, pow_succ]
    ring

end Codim2
