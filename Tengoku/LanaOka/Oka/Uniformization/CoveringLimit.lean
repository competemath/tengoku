/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.LanaOka.Oka.Uniformization.KoebeIteration
import Tengoku.LanaOka.Oka.Analytification.GAGA.Montel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The limit of the Koebe iteration is a universal covering by the disc

Let `Ω ⊆ ℂ` be open and connected and let `p₀` be a holomorphic covering map on `Ω` whose domain
`U₀ = p₀ ⁻¹' Ω` is an open subset of the unit disc `𝔻` containing `0` (`PlaneData`). Run the Koebe
iteration on `U₀` (`Oka/Uniformization/KoebeIteration.lean`) and rescale:
`Gₙ z = projₙ (ρₙ z)`, `ρₙ` the in-radius of `Uₙ`. The `Gₙ : 𝔻 → U₀` are uniformly bounded, so by
Montel a subsequence converges to `ϖ : 𝔻 → 𝔻`; by Hurwitz (each `Gₙ` omits every point outside
`U₀`, and `ϖ 0 = 0 ∈ U₀`) `ϖ` maps `𝔻` into `U₀`.

Put `ψ = p₀ ∘ ϖ`. For a disc `Δ ⊆ Ω` and `z ∈ 𝔻` with `ψ z ∈ Δ`, lift `Δ` through `p₀` and then
through `projₙ`, and rescale: this gives holomorphic sections `σₙ` of `Gₙ` over `Δ` through `z`,
bounded by `1/ρ₀`. A limit `σ` of these is a holomorphic section of `ψ` over `Δ` with `σ (ψ z) = z`,
and it maps `Δ` into `𝔻` by the maximum principle (`PlaneData.exists_section`). Local sections
through every point make `ψ` a covering map (`Uniformization.isCoveringMapOn_of_sections`).

## Main result

- `Uniformization.PlaneData.exists_covering`: a holomorphic covering map `ψ : 𝔻 → Ω`, onto, with
  nonvanishing derivative.
-/

open Complex Metric Set Filter Topology

namespace Uniformization

/-- The hypotheses of the plane uniformisation theorem: a holomorphic covering `p₀` of the open
connected set `Ω` whose domain `U₀` is an open subset of the unit disc containing `0`. -/
structure PlaneData (Ω U₀ : Set ℂ) (p₀ : ℂ → ℂ) : Prop where
  good : Good U₀
  isOpen : IsOpen Ω
  isPreconnected : IsPreconnected Ω
  covering : IsCoveringMapOn p₀ Ω
  preimage_eq : p₀ ⁻¹' Ω = U₀
  differentiableOn : DifferentiableOn ℂ p₀ U₀

variable {Ω U₀ : Set ℂ} {p₀ : ℂ → ℂ}

/-- A holomorphic function has a strict derivative at every point of an open set where it is
holomorphic. -/
theorem hasStrictDerivAt_of_differentiableOn {f : ℂ → ℂ} {U : Set ℂ} (hf : DifferentiableOn ℂ f U)
    (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) : HasStrictDerivAt f (deriv f z) z :=
  (hf.analyticAt (hU.mem_nhds hz)).hasStrictDerivAt

theorem PlaneData.deriv_ne_zero (h : PlaneData Ω U₀ p₀) {u : ℂ} (hu : u ∈ U₀) :
    deriv p₀ u ≠ 0 := by
  have hu' : u ∈ p₀ ⁻¹' Ω := h.preimage_eq ▸ hu
  obtain ⟨φ, huφ, hφ⟩ := h.covering.isLocalHomeomorphOn u hu'
  refine deriv_ne_zero_of_injOn (h.differentiableOn.mono inter_subset_right)
    (inter_mem (φ.open_source.mem_nhds huφ) (h.good.isOpen.mem_nhds hu)) ?_
  intro x hx y hy hxy
  rw [hφ] at hxy
  exact φ.injOn hx.1 hy.1 hxy

/-! ### The rescaled sequence and its limit -/

/-- The rescaled maps `Gₙ z = projₙ (ρₙ z)`, defined on the whole unit disc. -/
noncomputable def rescaled (U₀ : Set ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  proj U₀ n (inradius (seq U₀ n) * z)

theorem Good.mul_mem_seq (hU₀ : Good U₀) (n : ℕ) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    (inradius (seq U₀ n) : ℂ) * z ∈ seq U₀ n := by
  apply ball_inradius_subset
  have hρ := (hU₀.good_seq n).inradius_pos
  rw [mem_ball_zero_iff] at hz ⊢
  rw [norm_mul, Complex.norm_of_nonneg hρ.le]
  exact mul_lt_of_lt_one_right hρ hz

theorem Good.rescaled_mem (hU₀ : Good U₀) (n : ℕ) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    rescaled U₀ n z ∈ U₀ :=
  mapsTo_proj n (hU₀.mul_mem_seq n hz)

theorem Good.differentiableOn_rescaled (hU₀ : Good U₀) (n : ℕ) :
    DifferentiableOn ℂ (rescaled U₀ n) (ball 0 1) :=
  (hU₀.differentiableOn_proj n).comp ((differentiableOn_const _).mul differentiableOn_id)
    fun _ hz ↦ hU₀.mul_mem_seq n hz

theorem rescaled_zero (n : ℕ) : rescaled U₀ n 0 = 0 := by
  simp [rescaled, proj_zero]

theorem Good.tendsto_inradius (hU₀ : Good U₀) :
    Tendsto (fun n ↦ inradius (seq U₀ n)) atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hU₀.exists_ball_subset (R := 1 - ε / 2) (by linarith)
  refine ⟨N, fun n hn ↦ ?_⟩
  have h1 := le_inradius (hU₀.good_seq n) (hN n hn)
  have h2 := (hU₀.good_seq n).inradius_le_one
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- Reindexing a locally uniformly convergent sequence along a sequence of indices tending to
infinity. -/
theorem tendstoLocallyUniformlyOn_comp_atTop {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {s : Set ℂ}
    (h : TendstoLocallyUniformlyOn F f atTop s) {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) :
    TendstoLocallyUniformlyOn (fun j ↦ F (k j)) f atTop s := by
  intro u hu x hx
  obtain ⟨t, ht, hev⟩ := h u hu x hx
  exact ⟨t, ht, hk.eventually hev⟩

/-- **The limit map.** A subsequence of the rescaled maps converges locally uniformly on `𝔻` to a
holomorphic `ϖ` with `ϖ 0 = 0`, and `ϖ` maps `𝔻` into `U₀` (Hurwitz). -/
theorem Good.exists_limit (hU₀ : Good U₀) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ϖ : ℂ → ℂ, DifferentiableOn ℂ ϖ (ball 0 1) ∧
      TendstoLocallyUniformlyOn (fun k ↦ rescaled U₀ (φ k)) ϖ atTop (ball 0 1) ∧
      ϖ 0 = 0 ∧ MapsTo ϖ (ball 0 1) U₀ := by
  obtain ⟨ϖ, φ, hφ, hϖd, hlim⟩ := exists_subseq_tendstoLocallyUniformlyOn (E := ℂ) isOpen_ball
    (F := rescaled U₀) hU₀.differentiableOn_rescaled fun K hK _ ↦
      ⟨1, fun n x hx ↦ (mem_ball_zero_iff.mp (hU₀.subset_ball (hU₀.rescaled_mem n (hK hx)))).le⟩
  have h0 : ϖ 0 = 0 := by
    have := hlim.tendsto_comp (hϖd.continuousOn.continuousWithinAt (mem_ball_self one_pos))
      (mem_ball_self one_pos) (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        tendsto_const_nhds (Eventually.of_forall fun _ ↦ mem_ball_self one_pos))
    simp only [rescaled_zero] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  refine ⟨φ, hφ, ϖ, hϖd, hlim, h0, fun z hz ↦ ?_⟩
  by_contra hβ
  obtain ⟨r, hr, hrz⟩ := Metric.isOpen_iff.mp isOpen_ball z hz
  have hloc := eventually_eq_of_tendstoLocallyUniformlyOn (F := fun k ↦ rescaled U₀ (φ k))
    (β := ϖ z) hr (Eventually.of_forall fun k ↦ (hU₀.differentiableOn_rescaled _).mono hrz)
    (hlim.mono hrz) (Eventually.of_forall fun k w hw h ↦ hβ (h ▸ hU₀.rescaled_mem _ (hrz hw)))
    rfl
  have han : AnalyticOnNhd ℂ ϖ (ball 0 1) := hϖd.analyticOnNhd isOpen_ball
  have heq := han.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
    (convex_ball (0 : ℂ) 1).isPreconnected hz hloc
  have := heq (mem_ball_self one_pos)
  rw [h0] at this
  simp only at this
  exact hβ (by rw [← this]; exact hU₀.zero_mem)

/-! ### Sections -/

/-- The map `ψ = p₀ ∘ ϖ` on the disc, and the point `c₀ ∉ Ω` outside it. -/
noncomputable def limitMap (p₀ ϖ : ℂ → ℂ) (c₀ : ℂ) (z : ℂ) : ℂ := by
  classical
  exact if z ∈ ball (0 : ℂ) 1 then p₀ (ϖ z) else c₀

theorem limitMap_of_mem {ϖ : ℂ → ℂ} {c₀ z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    limitMap p₀ ϖ c₀ z = p₀ (ϖ z) := by
  simp [limitMap, hz]

/-- **Local sections of the limit.** For a disc `Δ = ball w ε ⊆ Ω` and `z ∈ 𝔻` with `ψ z ∈ Δ`,
there is a holomorphic section `σ : Δ → 𝔻` of `ψ` with `σ (ψ z) = z`. -/
theorem PlaneData.exists_section (h : PlaneData Ω U₀ p₀) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {ϖ : ℂ → ℂ} (hϖd : DifferentiableOn ℂ ϖ (ball 0 1))
    (hlim : TendstoLocallyUniformlyOn (fun k ↦ rescaled U₀ (φ k)) ϖ atTop (ball 0 1))
    (hϖU : MapsTo ϖ (ball 0 1) U₀) (c₀ : ℂ) {w : ℂ} {ε : ℝ} (hΔ : ball w ε ⊆ Ω) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hψz : limitMap p₀ ϖ c₀ z ∈ ball w ε) :
    ∃ σ : ℂ → ℂ, DifferentiableOn ℂ σ (ball w ε) ∧ MapsTo σ (ball w ε) (ball 0 1) ∧
      (∀ u ∈ ball w ε, limitMap p₀ ϖ c₀ (σ u) = u) ∧ σ (limitMap p₀ ϖ c₀ z) = z := by
  set Δ := ball w ε
  set ρ : ℕ → ℝ := fun n ↦ inradius (seq U₀ n)
  have hU₀ := h.good
  have hρ0 : ∀ n, 0 < ρ n := fun n ↦ (hU₀.good_seq n).inradius_pos
  have hρmono : ∀ n, ρ 0 ≤ ρ n := fun n ↦ hU₀.inradius_monotone (Nat.zero_le n)
  have hp₀c : ∀ u ∈ U₀, ContinuousAt p₀ u := fun u hu ↦
    h.differentiableOn.continuousOn.continuousAt (hU₀.isOpen.mem_nhds hu)
  rw [limitMap_of_mem hz] at hψz ⊢
  -- sections of `Gₙ` through `z` at level `n`, whenever `p₀ (Gₙ z) ∈ Δ`
  have hlevel : ∀ n, p₀ (rescaled U₀ n z) ∈ Δ → ∃ σ : ℂ → ℂ, DifferentiableOn ℂ σ Δ ∧
      (∀ u ∈ Δ, ‖σ u‖ ≤ 1 / ρ n) ∧ (∀ u ∈ Δ, p₀ (rescaled U₀ n (σ u)) = u ∧
        rescaled U₀ n (σ u) ∈ U₀) ∧ σ (p₀ (rescaled U₀ n z)) = z := by
    intro n hn
    set u₀ := p₀ (rescaled U₀ n z)
    have hGz : rescaled U₀ n z ∈ U₀ := hU₀.rescaled_mem n hz
    -- lift `Δ` through `p₀`
    obtain ⟨τ, hτc, hτp, hτ0⟩ := h.covering.exists_lift_of_convex (convex_ball w ε)
      continuousOn_id (fun u hu ↦ hΔ hu) hn (e₀ := rescaled U₀ n z) rfl
    have hτU : MapsTo τ Δ U₀ := fun u hu ↦ by
      rw [← h.preimage_eq, mem_preimage, hτp u hu]; exact hΔ hu
    have hτd : DifferentiableOn ℂ τ Δ := fun u hu ↦ by
      refine (differentiableAt_of_comp_eq (f := p₀) (g := id)
        (hasStrictDerivAt_of_differentiableOn h.differentiableOn hU₀.isOpen (hτU hu))
        (h.deriv_ne_zero (hτU hu)) (hτc.continuousAt (isOpen_ball.mem_nhds hu)) ?_
        differentiableAt_id).differentiableWithinAt
      filter_upwards [isOpen_ball.mem_nhds hu] with v hv using hτp v hv
    -- lift through `projₙ`
    obtain ⟨σ', hσ'c, hσ'm, hσ'p, hσ'0⟩ := hU₀.exists_lift n Δ (convex_ball w ε) τ hτc hτU u₀
      ((inradius (seq U₀ n) : ℂ) * z) hn (hU₀.mul_mem_seq n hz) (by rw [hτ0]; rfl)
    have hσ'd : DifferentiableOn ℂ σ' Δ := fun u hu ↦ by
      refine (differentiableAt_of_comp_eq (f := proj U₀ n) (g := τ)
        (hasStrictDerivAt_of_differentiableOn (hU₀.differentiableOn_proj n)
          (hU₀.good_seq n).isOpen (hσ'm hu))
        (hU₀.deriv_proj_ne_zero n (hσ'm hu)) (hσ'c.continuousAt (isOpen_ball.mem_nhds hu)) ?_
        ((hτd u hu).differentiableAt (isOpen_ball.mem_nhds hu))).differentiableWithinAt
      filter_upwards [isOpen_ball.mem_nhds hu] with v hv using hσ'p v hv
    have hρn : (inradius (seq U₀ n) : ℂ) ≠ 0 := by exact_mod_cast (hρ0 n).ne'
    refine ⟨fun u ↦ σ' u / inradius (seq U₀ n), hσ'd.div_const _, fun u hu ↦ ?_,
      fun u hu ↦ ?_, ?_⟩
    · have h1 := mem_ball_zero_iff.mp ((hU₀.good_seq n).subset_ball (hσ'm hu))
      rw [norm_div, Complex.norm_of_nonneg (hρ0 n).le]
      exact div_le_div_of_nonneg_right h1.le (hρ0 n).le
    · have : rescaled U₀ n (σ' u / inradius (seq U₀ n)) = τ u := by
        rw [rescaled, mul_div_cancel₀ _ hρn, hσ'p u hu]
      rw [this]
      exact ⟨hτp u hu, hτU hu⟩
    · simp only
      rw [hσ'0, mul_div_cancel_left₀ _ hρn]
  -- the level condition holds along the subsequence eventually
  have hconv : Tendsto (fun k ↦ p₀ (rescaled U₀ (φ k) z)) atTop (𝓝 (p₀ (ϖ z))) :=
    (hp₀c _ (hϖU hz)).tendsto.comp (hlim.tendsto_comp
      (hϖd.continuousOn.continuousWithinAt hz) hz
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ tendsto_const_nhds
        (Eventually.of_forall fun _ ↦ hz)))
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hconv.eventually (isOpen_ball.mem_nhds hψz))
  choose S hSd hSb hSp hS0 using fun j : ℕ ↦ hlevel (φ (j + K)) (hK (j + K) (by omega))
  -- Montel for the sections
  obtain ⟨σ, ψ₂, hψ₂, hσd, hσlim⟩ := exists_subseq_tendstoLocallyUniformlyOn (E := ℂ) isOpen_ball
    (F := S) hSd fun C hC _ ↦ ⟨1 / ρ 0, fun j x hx ↦ (hSb j x (hC hx)).trans
      (one_div_le_one_div_of_le (hρ0 0) (hρmono _))⟩
  set m : ℕ → ℕ := fun j ↦ φ (ψ₂ j + K)
  have hm : Tendsto m atTop atTop :=
    hφ.tendsto_atTop.comp ((tendsto_add_atTop_nat K).comp hψ₂.tendsto_atTop)
  have hGlim : TendstoLocallyUniformlyOn (fun j ↦ rescaled U₀ (m j)) ϖ atTop (ball 0 1) :=
    tendstoLocallyUniformlyOn_comp_atTop hlim
      ((tendsto_add_atTop_nat K).comp hψ₂.tendsto_atTop)
  -- `σ (ψ z) = z`
  have hσz : σ (p₀ (ϖ z)) = z := by
    have hu : Tendsto (fun j ↦ p₀ (rescaled U₀ (m j) z)) atTop (𝓝[Δ] (p₀ (ϖ z))) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (hconv.comp ((tendsto_add_atTop_nat K).comp hψ₂.tendsto_atTop))
        (Eventually.of_forall fun j ↦ hK _ (by omega))
    have := hσlim.tendsto_comp (hσd.continuousOn.continuousWithinAt hψz) hψz hu
    have hconst : (fun j ↦ S (ψ₂ j) (p₀ (rescaled U₀ (m j) z))) = fun _ ↦ z := by
      funext j; exact hS0 (ψ₂ j)
    rw [hconst] at this
    exact (tendsto_nhds_unique this tendsto_const_nhds)
  -- `|σ| ≤ 1` on `Δ`
  have hσle : ∀ u ∈ Δ, ‖σ u‖ ≤ 1 := by
    intro u hu
    have h1 : Tendsto (fun j ↦ S (ψ₂ j) u) atTop (𝓝 (σ u)) :=
      hσlim.tendsto_comp (hσd.continuousOn.continuousWithinAt hu) hu
        (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ tendsto_const_nhds
          (Eventually.of_forall fun _ ↦ hu))
    have h2 : Tendsto (fun j ↦ 1 / ρ (m j)) atTop (𝓝 1) := by
      simpa using (hU₀.tendsto_inradius.comp hm).inv₀ one_ne_zero
    refine le_of_tendsto_of_tendsto h1.norm h2 (Eventually.of_forall fun j ↦ ?_)
    exact hSb (ψ₂ j) u hu
  -- `σ` maps `Δ` into the open disc (maximum principle)
  have hσD : MapsTo σ Δ (ball 0 1) := by
    intro u hu
    rw [mem_ball_zero_iff]
    by_contra hge
    have hmax : IsMaxOn (norm ∘ σ) Δ u := fun v hv ↦ by
      simp only [mem_ofPred_eq, Function.comp_apply]
      exact (hσle v hv).trans (not_lt.mp hge)
    have hc := eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball w ε).isPreconnected isOpen_ball
      hσd hu hmax hψz
    rw [hσz] at hc
    simp only [Function.const_apply] at hc
    rw [hc] at hz
    exact hge (mem_ball_zero_iff.mp hz)
  -- `ψ ∘ σ = id` on `Δ`
  have hσsec : ∀ u ∈ Δ, p₀ (ϖ (σ u)) = u := by
    intro u hu
    have h1 : Tendsto (fun j ↦ S (ψ₂ j) u) atTop (𝓝[ball 0 1] (σ u)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · exact hσlim.tendsto_comp (hσd.continuousOn.continuousWithinAt hu) hu
          (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ tendsto_const_nhds
            (Eventually.of_forall fun _ ↦ hu))
      · exact (hσlim.tendsto_comp (hσd.continuousOn.continuousWithinAt hu) hu
          (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ tendsto_const_nhds
            (Eventually.of_forall fun _ ↦ hu))).eventually (isOpen_ball.mem_nhds (hσD hu))
    have h2 := hGlim.tendsto_comp (hϖd.continuousOn.continuousWithinAt (hσD hu)) (hσD hu) h1
    have h3 := (hp₀c _ (hϖU (hσD hu))).tendsto.comp h2
    have hconst : (p₀ ∘ fun j ↦ rescaled U₀ (m j) (S (ψ₂ j) u)) = fun _ ↦ u := by
      funext j; exact (hSp (ψ₂ j) u hu).1
    rw [hconst] at h3
    exact (tendsto_nhds_unique h3 tendsto_const_nhds)
  refine ⟨σ, hσd, hσD, fun u hu ↦ ?_, hσz⟩
  rw [limitMap_of_mem (hσD hu)]
  exact hσsec u hu

end Uniformization
