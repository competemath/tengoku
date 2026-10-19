/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.LanaOka.Oka.Analytic.LeviExtension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Directions avoiding the poles of a meromorphic function

Let `E` be a finite-dimensional complex normed space, `g` analytic on a ball about the origin and
not identically zero near the origin, and let `f` be locally a quotient of holomorphic functions
(`IsLocallyQuotientAt`) near every point of the ball at which `g` does not vanish. We show that
in every nonempty open set of nonzero directions there is a direction `v` such that `g` does not
vanish identically on the line through `v`, and such that for arbitrarily small `r > 0` the
function `f` is analytic at every point of the circle `{t • v | ‖t‖ = r}`
(`exists_direction_forall_analyticAt`).

This is the choice of coordinates in the extension of meromorphic functions across sets of
codimension two: the circles over which the Cauchy integrals are taken must avoid the poles.

## Proof

Both properties define countably many open subsets of the space of directions, and we show that
each of them is dense; Baire's theorem then gives a direction with all properties. Density of the
directions of lines on which `g` does not vanish identically follows from the identity theorem,
since a family of lines on which `g` vanishes near the origin, parametrised by an open set of
directions, sweeps out an open set. For the circles: if on an open set of directions every circle
of radius in `[α, β]` met the poles, then on every such line the poles would accumulate, so a
local denominator would vanish identically on a segment of the line. By Baire's theorem this
happens for one local denominator on an open set of directions and a common segment, so the
denominator vanishes on an open set, which is impossible.

## Main results

- `exists_isOpen_subset_inter_of_subset_iUnion`, `nonempty_inter_iInter_of_isOpen`: two forms of
  Baire's theorem relative to an open set.
- `exists_mem_frequently_smul_ne_zero`: directions of lines on which `g` does not vanish
  identically are dense.
- `exists_mem_forall_analyticAt_smul`: directions with a circle avoiding the poles of `f` are
  dense.
- `exists_direction_forall_analyticAt`: the combination.
-/

open Set Filter Metric
open scoped Topology Pointwise

section Baire

variable {X : Type*} [TopologicalSpace X] [BaireSpace X]

/-- **Baire's theorem** relative to an open set: if a nonempty open set is covered by countably
many closed sets, one of them contains a nonempty open subset of it. -/
theorem exists_isOpen_subset_inter_of_subset_iUnion {ι : Type*} [Countable ι] {Y : ι → Set X}
    (hY : ∀ i, IsClosed (Y i)) {V : Set X} (hV : IsOpen V) (hVne : V.Nonempty)
    (hcov : V ⊆ ⋃ i, Y i) : ∃ i, ∃ W, IsOpen W ∧ W.Nonempty ∧ W ⊆ V ∩ Y i := by
  obtain ⟨x₀, hx₀⟩ := hVne
  obtain ⟨i₀, -⟩ := mem_iUnion.mp (hcov hx₀)
  have hU : ⋃ i, (Y i ∪ Vᶜ) = univ := eq_univ_of_forall fun x ↦ by
    by_cases hx : x ∈ V
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov hx)
      exact mem_iUnion.mpr ⟨i, Or.inl hi⟩
    · exact mem_iUnion.mpr ⟨i₀, Or.inr hx⟩
  obtain ⟨x, hxV, hx⟩ := (dense_iUnion_interior_of_closed
    (fun i ↦ (hY i).union hV.isClosed_compl) hU).inter_open_nonempty V hV ⟨x₀, hx₀⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  refine ⟨i, V ∩ interior (Y i ∪ Vᶜ), hV.inter isOpen_interior, ⟨x, hxV, hi⟩,
    fun y hy ↦ ⟨hy.1, ?_⟩⟩
  rcases interior_subset hy.2 with h | h
  · exact h
  · exact absurd hy.1 h

/-- **Baire's theorem** relative to an open set: countably many open sets which are dense in a
nonempty open set `V` have a common point in `V`. -/
theorem nonempty_inter_iInter_of_isOpen {ι : Type*} [Countable ι] {O : ι → Set X}
    (hO : ∀ i, IsOpen (O i)) {V : Set X} (hV : IsOpen V) (hVne : V.Nonempty)
    (hdense : ∀ i, ∀ W, IsOpen W → W.Nonempty → W ⊆ V → (W ∩ O i).Nonempty) :
    (V ∩ ⋂ i, O i).Nonempty := by
  have hd : ∀ i, Dense (O i ∪ (closure V)ᶜ) := fun i ↦ by
    refine dense_iff_inter_open.mpr fun U hU hUne ↦ ?_
    by_cases hUV : (U ∩ V).Nonempty
    · obtain ⟨x, hx⟩ := hdense i (U ∩ V) (hU.inter hV) hUV inter_subset_right
      exact ⟨x, hx.1.1, Or.inl hx.2⟩
    · obtain ⟨x, hx⟩ := hUne
      refine ⟨x, hx, Or.inr fun hxc ↦ ?_⟩
      have := hU.inter_closure ⟨hx, hxc⟩
      rw [not_nonempty_iff_eq_empty.mp hUV, closure_empty] at this
      exact this
  obtain ⟨x, hx⟩ := (dense_iInter_of_isOpen (fun i ↦ (hO i).union isClosed_closure.isOpen_compl)
    hd).inter_open_nonempty V hV hVne
  refine ⟨x, hx.1, mem_iInter.mpr fun i ↦ ?_⟩
  rcases mem_iInter.mp hx.2 i with h | h
  · exact h
  · exact absurd (subset_closure hx.1) h

end Baire

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The union of the dilates `s • W` of an open set by the elements of a set of nonzero scalars is
open. -/
theorem isOpen_biUnion_smul {Δ : Set ℂ} (h0 : (0 : ℂ) ∉ Δ) {W : Set E} (hW : IsOpen W) :
    IsOpen (⋃ s ∈ Δ, s • W) :=
  isOpen_biUnion fun _ hs ↦ hW.smul₀ fun h ↦ h0 (h ▸ hs)

variable [FiniteDimensional ℂ E]

/-- If `f = u / w` on a ball with `u` and `w` holomorphic, then `f` is analytic at every point of
the ball at which `w` does not vanish. -/
theorem analyticAt_of_eq_div {f u w : E → ℂ} {z : E} {η : ℝ}
    (hu : DifferentiableOn ℂ u (ball z η)) (hw : DifferentiableOn ℂ w (ball z η))
    (hf : ∀ y ∈ ball z η, w y ≠ 0 → f y = u y / w y) {y : E} (hy : y ∈ ball z η)
    (hwy : w y ≠ 0) : AnalyticAt ℂ f y := by
  have hO : IsOpen (ball z η ∩ w ⁻¹' {0}ᶜ) :=
    hw.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton
  have hd : DifferentiableOn ℂ (fun y ↦ u y * (w y)⁻¹) (ball z η ∩ w ⁻¹' {0}ᶜ) :=
    (hu.mono inter_subset_left).mul ((hw.mono inter_subset_left).inv fun y hy ↦ hy.2)
  refine (analyticAt_of_differentiableOn_of_finiteDimensional hO hd ⟨hy, hwy⟩).congr ?_
  filter_upwards [hO.mem_nhds ⟨hy, hwy⟩] with y' hy'
  rw [hf y' hy'.1 hy'.2, div_eq_mul_inv]

/-- In every nonempty open set of directions there is a direction `v` such that `g` does not
vanish identically near the origin on the line through `v`, provided `g` is analytic on a ball
about the origin and does not vanish identically near the origin. -/
theorem exists_mem_frequently_smul_ne_zero {g : E → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hg : AnalyticOnNhd ℂ g (ball 0 ρ)) (hg0 : ∃ᶠ z in 𝓝 0, g z ≠ 0) {V : Set E}
    (hV : IsOpen V) (hVne : V.Nonempty) : ∃ v ∈ V, ∃ᶠ t in 𝓝 (0 : ℂ), g (t • v) ≠ 0 := by
  haveI := FiniteDimensional.complete ℂ E
  by_contra! H
  obtain ⟨v₁, hv₁⟩ := hVne
  obtain ⟨κ, hκ, hκV⟩ := Metric.isOpen_iff.mp hV v₁ hv₁
  set M : ℝ := ‖v₁‖ + κ + 1
  have hM : 0 < M := by positivity
  have hvM : ∀ v ∈ closedBall v₁ κ, ‖v‖ < M := fun v hv ↦ by
    have := norm_le_norm_add_norm_sub' v v₁
    rw [mem_closedBall, dist_eq_norm] at hv
    simp only [M]
    linarith
  set τ : ℕ → ℝ := fun m ↦ ρ / (2 * M) / (m + 1)
  have hτ : ∀ m, 0 < τ m := fun m ↦ by positivity
  have hτM : ∀ m, τ m * M ≤ ρ / 2 := fun m ↦ by
    simp only [τ]
    rw [div_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
    nlinarith [mul_nonneg (mul_pos hρ hM).le (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hsmul : ∀ m, ∀ t ∈ closedBall (0 : ℂ) (τ m), ∀ v ∈ closedBall v₁ κ,
      t • v ∈ ball (0 : E) ρ := fun m t ht v hv ↦ by
    rw [mem_ball_zero_iff, norm_smul]
    rw [mem_closedBall_zero_iff] at ht
    calc ‖t‖ * ‖v‖ ≤ τ m * M := mul_le_mul ht (hvM v hv).le (norm_nonneg _) (hτ m).le
      _ ≤ ρ / 2 := hτM m
      _ < ρ := half_lt_self hρ
  set Y : ℕ → Set E := fun m ↦ ⋂ t ∈ closedBall (0 : ℂ) (τ m),
    closedBall v₁ κ ∩ (fun v ↦ g (t • v)) ⁻¹' {0}
  have hYc : ∀ m, IsClosed (Y m) := fun m ↦ isClosed_biInter fun t ht ↦
    ContinuousOn.preimage_isClosed_of_isClosed
      (hg.continuousOn.comp (by fun_prop) fun v hv ↦ hsmul m t ht v hv) isClosed_closedBall
      isClosed_singleton
  have hcov : ball v₁ κ ⊆ ⋃ m, Y m := fun v hv ↦ by
    obtain ⟨ε, hε, hεv⟩ := Metric.eventually_nhds_iff.mp (H v (hκV hv))
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (div_pos hε (div_pos hρ (by positivity : 0 < 2 * M)))
    refine mem_iUnion.mpr ⟨m, mem_iInter₂.mpr fun t ht ↦ ⟨ball_subset_closedBall hv, ?_⟩⟩
    refine hεv ?_
    rw [dist_zero_right]
    refine (mem_closedBall_zero_iff.mp ht).trans_lt ?_
    have h2M : 0 < ρ / (2 * M) := div_pos hρ (by positivity)
    calc τ m = ρ / (2 * M) * (1 / (m + 1)) := by simp only [τ]; ring
      _ < ρ / (2 * M) * (ε / (ρ / (2 * M))) := mul_lt_mul_of_pos_left hm h2M
      _ = ε := by field_simp
  obtain ⟨m, W, hW, ⟨w₀, hw₀⟩, hWsub⟩ :=
    exists_isOpen_subset_inter_of_subset_iUnion hYc isOpen_ball ⟨v₁, mem_ball_self hκ⟩ hcov
  set Δ : Set ℂ := ball ((τ m / 2 : ℝ) : ℂ) (τ m / 4)
  have hΔ : ∀ s ∈ Δ, s ∈ closedBall (0 : ℂ) (τ m) := fun s hs ↦ by
    rw [mem_closedBall_zero_iff]
    have h1 := norm_le_norm_add_norm_sub' s ((τ m / 2 : ℝ) : ℂ)
    rw [mem_ball, dist_eq_norm] at hs
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith [hτ m])] at h1
    linarith [hτ m]
  have hΔ0 : (0 : ℂ) ∉ Δ := fun h ↦ by
    rw [mem_ball, dist_zero_left, Complex.norm_real, Real.norm_of_nonneg (by linarith [hτ m])]
      at h
    linarith [hτ m]
  have hO := isOpen_biUnion_smul hΔ0 hW
  have hmem : ((τ m / 2 : ℝ) : ℂ) • w₀ ∈ ⋃ s ∈ Δ, s • W :=
    mem_biUnion (mem_ball_self (by linarith [hτ m])) (smul_mem_smul_set hw₀)
  have hz : ∀ y ∈ ⋃ s ∈ Δ, s • W, y ∈ ball (0 : E) ρ ∧ g y = 0 := fun y hy ↦ by
    obtain ⟨s, hs, v, hv, rfl⟩ : ∃ s ∈ Δ, ∃ v ∈ W, s • v = y := by
      simpa [Set.mem_smul] using hy
    have hvY := mem_iInter₂.mp (hWsub hv).2 s (hΔ s hs)
    exact ⟨hsmul m s (hΔ s hs) v hvY.1, hvY.2⟩
  have hball := hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball 0 ρ).isPreconnected
    (hz _ hmem).1 (Filter.mem_of_superset (hO.mem_nhds hmem) fun y hy ↦ (hz y hy).2)
  exact hg0 (Filter.mem_of_superset (ball_mem_nhds 0 hρ) fun z hz ↦ by simpa using hball hz)

/-- Let `g` be analytic on a ball about the origin and not identically zero near the origin, and
let `f` be locally a quotient near every point of the ball at which `g` does not vanish. Then in
every nonempty open set `V` of nonzero directions there is a direction `v` and a radius
`0 < r < ε` such that `f` is analytic at every point of the circle `{t • v | ‖t‖ = r}`. -/
theorem exists_mem_forall_analyticAt_smul {g f : E → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hg : AnalyticOnNhd ℂ g (ball 0 ρ)) (hg0 : ∃ᶠ z in 𝓝 0, g z ≠ 0)
    (hq : ∀ z ∈ ball (0 : E) ρ, g z ≠ 0 → IsLocallyQuotientAt f z) {V : Set E}
    (hV : IsOpen V) (hVne : V.Nonempty) (hV0 : (0 : E) ∉ V) {ε : ℝ} (hε : 0 < ε) :
    ∃ v ∈ V, ∃ r ∈ Ioo 0 ε, ∀ t : ℂ, ‖t‖ = r → AnalyticAt ℂ f (t • v) := by
  classical
  haveI := FiniteDimensional.complete ℂ E
  obtain ⟨v₁, hv₁V, hv₁g⟩ := exists_mem_frequently_smul_ne_zero hρ hg hg0 hV hVne
  -- `g` has an isolated zero at the origin on the line through `v₁`
  have han : AnalyticAt ℂ (fun t : ℂ ↦ g (t • v₁)) 0 := by
    have h0 : AnalyticAt ℂ g ((0 : ℂ) • v₁) := by simpa using hg 0 (mem_ball_self hρ)
    exact AnalyticAt.comp (f := fun t : ℂ ↦ t • v₁) (x := 0) h0
      (show AnalyticAt ℂ (fun t : ℂ ↦ t • v₁) 0 from analyticAt_id.smul analyticAt_const)
  have hiso : ∀ᶠ t in 𝓝[≠] (0 : ℂ), g (t • v₁) ≠ 0 :=
    han.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun h ↦
      hv₁g (h.mono fun t ht ↦ not_not.mpr ht)
  obtain ⟨τ₁, hτ₁, hτ₁g⟩ : ∃ τ > 0, ∀ t : ℂ, t ≠ 0 → ‖t‖ < τ → g (t • v₁) ≠ 0 := by
    obtain ⟨τ, hτ, h⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hiso)
    exact ⟨τ, hτ, fun t ht0 ht ↦ h (by simpa using ht) ht0⟩
  -- an annulus of radii on which `g` does not vanish on nearby lines
  set β : ℝ := min (min τ₁ ε) (ρ / (‖v₁‖ + 1)) / 2
  set α : ℝ := β / 2
  have hm : 0 < min (min τ₁ ε) (ρ / (‖v₁‖ + 1)) := lt_min (lt_min hτ₁ hε) (by positivity)
  have hβ : 0 < β := half_pos hm
  have hα : 0 < α := half_pos hβ
  have hαβ : α < β := half_lt_self hβ
  have hβm : β < min (min τ₁ ε) (ρ / (‖v₁‖ + 1)) := half_lt_self hm
  have hβτ : β < τ₁ := hβm.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hβε : β < ε := hβm.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hβρ : β * (‖v₁‖ + 1) < ρ :=
    (lt_div_iff₀ (by positivity)).mp (hβm.trans_le (min_le_right _ _))
  set K₁ : Set ℂ := {t | α ≤ ‖t‖ ∧ ‖t‖ ≤ β}
  have hK₁ : IsCompact K₁ := (isCompact_closedBall (0 : ℂ) β).of_isClosed_subset
    ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const))
    fun t ht ↦ mem_closedBall_zero_iff.mpr ht.2
  have hK₁0 : ∀ t ∈ K₁, t ≠ 0 := fun t ht ↦ norm_pos_iff.mp (hα.trans_le ht.1)
  have htube : ∀ᶠ v in 𝓝 v₁, ∀ t ∈ K₁, t • v ∈ ball (0 : E) ρ ∧ g (t • v) ≠ 0 := by
    refine hK₁.eventually_forall_of_forall_eventually fun t ht ↦ ?_
    have hmem : t • v₁ ∈ ball (0 : E) ρ := by
      rw [mem_ball_zero_iff, norm_smul]
      calc ‖t‖ * ‖v₁‖ ≤ β * (‖v₁‖ + 1) :=
            mul_le_mul ht.2 (by linarith) (norm_nonneg _) hβ.le
        _ < ρ := hβρ
    have hcont : ContinuousAt (fun z : E × ℂ ↦ z.2 • z.1) (v₁, t) := by fun_prop
    exact (show ∀ᶠ z : E × ℂ in 𝓝 (v₁, t), z.2 • z.1 ∈ ball (0 : E) ρ from
      hcont.preimage_mem_nhds (isOpen_ball.mem_nhds hmem)).and
      ((ContinuousAt.comp (f := fun z : E × ℂ ↦ z.2 • z.1) (x := (v₁, t))
        (hg _ hmem).continuousAt hcont).eventually_ne
        (hτ₁g t (hK₁0 t ht) (ht.2.trans_lt hβτ)))
  obtain ⟨κ, hκ, hκsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (htube.and (hV.mem_nhds hv₁V))
  by_contra! Hbad
  -- the compact set swept out by the annuli on nearby lines, covered by local quotients
  set K₂ : Set E := (fun p : ℂ × E ↦ p.1 • p.2) '' (K₁ ×ˢ closedBall v₁ κ)
  have hK₂ : IsCompact K₂ := (hK₁.prod (isCompact_closedBall v₁ κ)).image (by fun_prop)
  have hK₂prop : ∀ z ∈ K₂, z ∈ ball (0 : E) ρ ∧ g z ≠ 0 ∧ z ≠ 0 := by
    rintro _ ⟨⟨t, v⟩, ⟨ht, hv⟩, rfl⟩
    obtain ⟨h1, h2⟩ := (hκsub hv).1 t ht
    exact ⟨h1, h2, smul_ne_zero (hK₁0 t ht) fun h ↦ hV0 (h ▸ (hκsub hv).2)⟩
  choose! η hη u w hu hw hw0 hf using fun z (hz : z ∈ K₂) ↦
    (hq z (hK₂prop z hz).1 (hK₂prop z hz).2.1).exists_ball
  set η' : E → ℝ := fun z ↦ min (η z) (‖z‖ / 2)
  have hη' : ∀ z ∈ K₂, 0 < η' z := fun z hz ↦
    lt_min (hη z hz) (half_pos (norm_pos_iff.mpr (hK₂prop z hz).2.2))
  have hη'η : ∀ z, ball z (η' z) ⊆ ball z (η z) := fun z ↦ ball_subset_ball (min_le_left _ _)
  obtain ⟨Z, hZK, hZcov⟩ := hK₂.elim_nhds_subcover (fun z ↦ ball z (η' z / 2))
    fun z hz ↦ ball_mem_nhds z (half_pos (hη' z hz))
  obtain ⟨Q, hQc, hQd⟩ := TopologicalSpace.exists_countable_dense ℂ
  haveI : Countable Q := hQc.to_subtype
  -- the directions whose lines meet a common segment on which one local denominator vanishes
  set Y : Z × Q × ℕ → Set E := fun i ↦ ⋂ s ∈ closedBall (i.2.1 : ℂ) (1 / ((i.2.2 : ℝ) + 1)),
    closedBall v₁ κ ∩ (fun v ↦ s • v) ⁻¹' (closedBall (i.1 : E) (3 * η' i.1 / 4) ∩ w i.1 ⁻¹' {0})
  have hC : ∀ z ∈ K₂, IsClosed (closedBall z (3 * η' z / 4) ∩ w z ⁻¹' {0}) := fun z hz ↦
    ContinuousOn.preimage_isClosed_of_isClosed ((hw z hz).continuousOn.mono
      ((closedBall_subset_ball (by linarith [hη' z hz])).trans (hη'η z))) isClosed_closedBall
      isClosed_singleton
  have hYc : ∀ i, IsClosed (Y i) := fun i ↦ isClosed_biInter fun s _ ↦
    isClosed_closedBall.inter ((hC i.1 (hZK _ i.1.2)).preimage (continuous_const_smul s))
  have hcov : ball v₁ κ ⊆ ⋃ i, Y i := by
    intro v hv
    have hvc : v ∈ closedBall v₁ κ := ball_subset_closedBall hv
    have hvV : v ∈ V := (hκsub hvc).2
    -- the radii of the poles on the line through `v` fill `[α, β]`, so the poles accumulate
    set T : Set ℂ := {t ∈ K₁ | ¬AnalyticAt ℂ f (t • v)}
    have hTc : IsClosed T := hK₁.isClosed.inter
      ((isOpen_analyticAt ℂ f).preimage (continuous_id.smul continuous_const)).isClosed_compl
    have hTinf : T.Infinite := by
      refine Set.Infinite.of_image norm ((Set.Icc_infinite hαβ).mono fun r hr ↦ ?_)
      obtain ⟨t, htr, ht⟩ := Hbad v hvV r ⟨hα.trans_le hr.1, hr.2.trans_lt hβε⟩
      exact ⟨t, ⟨⟨htr ▸ hr.1, htr ▸ hr.2⟩, ht⟩, htr⟩
    obtain ⟨t₀, ht₀K, hacc⟩ := hTinf.exists_accPt_of_subset_isCompact hK₁ fun t ht ↦ ht.1
    rw [accPt_iff_frequently] at hacc
    have ht₀K₂ : t₀ • v ∈ K₂ := ⟨(t₀, v), ⟨ht₀K, hvc⟩, rfl⟩
    obtain ⟨z, hzZ, hz⟩ : ∃ z ∈ Z, t₀ • v ∈ ball z (η' z / 2) := by simpa using hZcov ht₀K₂
    have hzK := hZK z hzZ
    set Ω : Set ℂ := (fun s : ℂ ↦ s • v) ⁻¹' ball z (η' z)
    have hΩ : IsOpen Ω := isOpen_ball.preimage (continuous_id.smul continuous_const)
    have ht₀Ω : t₀ ∈ Ω := ball_subset_ball (half_le_self (hη' z hzK).le) hz
    have hψ : AnalyticAt ℂ (fun s : ℂ ↦ w z (s • v)) t₀ :=
      DifferentiableOn.analyticAt (((hw z hzK).mono (hη'η z)).comp
        (by fun_prop : DifferentiableOn ℂ (fun s : ℂ ↦ s • v) Ω) fun s hs ↦ hs)
        (hΩ.mem_nhds ht₀Ω)
    -- the local denominator vanishes near `t₀` on the line
    have hψ0 : ∀ᶠ s in 𝓝 t₀, w z (s • v) = 0 := by
      refine hψ.eventually_eq_zero_or_eventually_ne_zero.resolve_right fun hne ↦ ?_
      obtain ⟨s, ⟨⟨hst, hsT⟩, hsne⟩, hsΩ⟩ := ((hacc.and_eventually
        (eventually_nhdsWithin_iff.mp hne)).and_eventually (hΩ.mem_nhds ht₀Ω)).exists
      exact hsT.2 (analyticAt_of_eq_div (hu z hzK) (hw z hzK) (hf z hzK) (hη'η z hsΩ)
        (hsne hst))
    have hnear : ∀ᶠ s in 𝓝 t₀, w z (s • v) = 0 ∧ s • v ∈ ball z (3 * η' z / 4) :=
      hψ0.and ((continuous_id.smul continuous_const).continuousAt.preimage_mem_nhds
        (isOpen_ball.mem_nhds (ball_subset_ball (by linarith [hη' z hzK]) hz)))
    obtain ⟨ε', hε', hε'sub⟩ := Metric.eventually_nhds_iff.mp hnear
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hε')
    obtain ⟨q, hqQ, hq⟩ := hQd.exists_dist_lt t₀ (half_pos hε')
    refine mem_iUnion.mpr ⟨(⟨z, hzZ⟩, ⟨q, hqQ⟩, k), mem_iInter₂.mpr fun s hs ↦ ⟨hvc, ?_⟩⟩
    have hs' : dist s t₀ < ε' := by
      rw [mem_closedBall] at hs
      rw [dist_comm] at hq
      linarith [dist_triangle s q t₀]
    obtain ⟨h1, h2⟩ := hε'sub hs'
    exact ⟨ball_subset_closedBall h2, h1⟩
  -- Baire's theorem: one local denominator vanishes on an open set
  obtain ⟨⟨⟨z, hzZ⟩, ⟨q, hqQ⟩, k⟩, W, hW, ⟨v₀, hv₀⟩, hWsub⟩ :=
    exists_isOpen_subset_inter_of_subset_iUnion hYc isOpen_ball ⟨v₁, mem_ball_self hκ⟩ hcov
  have hzK := hZK z hzZ
  set Δ : Set ℂ := ball q (1 / ((k : ℝ) + 1))
  have hY : ∀ v ∈ W, ∀ s ∈ Δ, s • v ∈ closedBall z (3 * η' z / 4) ∧ w z (s • v) = 0 :=
    fun v hv s hs ↦ (mem_iInter₂.mp (hWsub hv).2 s (ball_subset_closedBall hs)).2
  have hsmall : ∀ y ∈ closedBall z (3 * η' z / 4), y ≠ 0 := fun y hy h0 ↦ by
    rw [h0, mem_closedBall, dist_zero_left] at hy
    have h1 : η' z ≤ ‖z‖ / 2 := min_le_right _ _
    have h2 : 0 < ‖z‖ := norm_pos_iff.mpr (hK₂prop z hzK).2.2
    linarith
  have hΔ0 : (0 : ℂ) ∉ Δ := fun h ↦ hsmall _ (hY v₀ hv₀ 0 h).1 (zero_smul ℂ v₀)
  have hq_mem : q • v₀ ∈ ⋃ s ∈ Δ, s • W :=
    mem_biUnion (mem_ball_self (by positivity)) (smul_mem_smul_set hv₀)
  have hOsub : (⋃ s ∈ Δ, s • W) ⊆ ball z (η z) ∩ w z ⁻¹' {0} := fun y hy ↦ by
    obtain ⟨s, hs, v, hv, rfl⟩ : ∃ s ∈ Δ, ∃ v ∈ W, s • v = y := by
      simpa [Set.mem_smul] using hy
    obtain ⟨h1, h2⟩ := hY v hv s hs
    exact ⟨hη'η z (closedBall_subset_ball (by linarith [hη' z hzK]) h1), h2⟩
  have := interior_maximal hOsub (isOpen_biUnion_smul hΔ0 hW) hq_mem
  rw [hw0 z hzK] at this
  exact this

/-- **Choice of a direction.** Let `g` be analytic on a ball about the origin and not identically
zero near the origin, and let `f` be locally a quotient near every point of the ball at which `g`
does not vanish. Then every nonempty open set `V` of nonzero directions contains a direction `v`
such that `g` does not vanish identically near the origin on the line through `v`, and such that
for every `ε > 0` there is a radius `0 < r < ε` for which `f` is analytic at every point of the
circle `{t • v | ‖t‖ = r}`. -/
theorem exists_direction_forall_analyticAt {g f : E → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hg : AnalyticOnNhd ℂ g (ball 0 ρ)) (hg0 : ∃ᶠ z in 𝓝 0, g z ≠ 0)
    (hq : ∀ z ∈ ball (0 : E) ρ, g z ≠ 0 → IsLocallyQuotientAt f z) {V : Set E}
    (hV : IsOpen V) (hVne : V.Nonempty) (hV0 : (0 : E) ∉ V) :
    ∃ v ∈ V, (∃ᶠ t in 𝓝 (0 : ℂ), g (t • v) ≠ 0) ∧
      ∀ ε > 0, ∃ r ∈ Ioo 0 ε, ∀ t : ℂ, ‖t‖ = r → AnalyticAt ℂ f (t • v) := by
  haveI := FiniteDimensional.complete ℂ E
  set O : ℕ ⊕ ℕ → Set E := fun i ↦ i.elim
    (fun m : ℕ ↦ ⋃ t ∈ ball (0 : ℂ) (1 / ((m : ℝ) + 1)),
      {v | t • v ∈ ball (0 : E) ρ ∧ g (t • v) ≠ 0})
    (fun m : ℕ ↦ {v | ∃ r ∈ Ioo 0 (1 / ((m : ℝ) + 1)),
      ∀ t : ℂ, ‖t‖ = r → AnalyticAt ℂ f (t • v)})
  have hO : ∀ i, IsOpen (O i) := by
    rintro (m | m)
    · refine isOpen_biUnion fun t _ ↦ ?_
      exact (hg.continuousOn.comp (continuous_const_smul t).continuousOn fun v hv ↦ hv)
        |>.isOpen_inter_preimage (isOpen_ball.preimage (continuous_const_smul t))
          isOpen_compl_singleton
    · refine isOpen_iff_mem_nhds.mpr fun v ⟨r, hr, hv⟩ ↦ ?_
      have hK := isCompact_sphere (0 : ℂ) r
      have : ∀ᶠ v' in 𝓝 v, ∀ t ∈ sphere (0 : ℂ) r, AnalyticAt ℂ f (t • v') := by
        refine hK.eventually_forall_of_forall_eventually fun t ht ↦ ?_
        have hcont : ContinuousAt (fun z : E × ℂ ↦ z.2 • z.1) (v, t) := by fun_prop
        exact hcont.preimage_mem_nhds ((isOpen_analyticAt ℂ f).mem_nhds
          (hv t (mem_sphere_zero_iff_norm.mp ht)))
      filter_upwards [this] with v' hv'
      exact ⟨r, hr, fun t ht ↦ hv' t (mem_sphere_zero_iff_norm.mpr ht)⟩
  have hdense : ∀ i, ∀ W, IsOpen W → W.Nonempty → W ⊆ V → (W ∩ O i).Nonempty := by
    rintro (m | m) W hW hWne hWV
    · obtain ⟨v, hvW, hv⟩ := exists_mem_frequently_smul_ne_zero hρ hg hg0 hW hWne
      have hsmall : ∀ᶠ t in 𝓝 (0 : ℂ), t ∈ ball (0 : ℂ) (1 / ((m : ℝ) + 1)) ∧
          t • v ∈ ball (0 : E) ρ := by
        refine Filter.Eventually.and (ball_mem_nhds _ (by positivity)) ?_
        have hcont : ContinuousAt (fun t : ℂ ↦ t • v) 0 := by fun_prop
        exact hcont.preimage_mem_nhds (by simpa using ball_mem_nhds (0 : E) hρ)
      obtain ⟨t, ht, ht1, ht2⟩ := (hv.and_eventually hsmall).exists
      exact ⟨v, hvW, mem_biUnion ht1 ⟨ht2, ht⟩⟩
    · obtain ⟨v, hvW, r, hr, hv⟩ := exists_mem_forall_analyticAt_smul hρ hg hg0 hq hW hWne
        (fun h ↦ hV0 (hWV h)) (by positivity : (0 : ℝ) < 1 / ((m : ℝ) + 1))
      exact ⟨v, hvW, r, hr, hv⟩
  obtain ⟨v, hvV, hv⟩ := nonempty_inter_iInter_of_isOpen hO hV hVne hdense
  have hvO : ∀ i, v ∈ O i := mem_iInter.mp hv
  refine ⟨v, hvV, ?_, fun ε hε ↦ ?_⟩
  · rw [Filter.frequently_iff]
    intro U hU
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    obtain ⟨t, ht, -, hgt⟩ := mem_iUnion₂.mp (hvO (Sum.inl m))
    exact ⟨t, hεU (ball_subset_ball hm.le ht), hgt⟩
  · obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    obtain ⟨r, hr, hrv⟩ := hvO (Sum.inr m)
    exact ⟨r, ⟨hr.1, hr.2.trans hm⟩, hrv⟩
