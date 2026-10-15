/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.JacobianConstruction.ChartedSpaceKitV
public import Tengoku

/-!
# The abstract torus layer: `V ⧸ L` for `L : AddSubgroup V`

Unit: jacobian-construction (`docs/design/jacobian-construction.md` §3–§9). This is the reusable
core of the whole unit: for a complex normed space `V` (always instantiated at `Fin n → ℂ`) and an
additive subgroup `L`, we build:

* `AddCommGroup`/`TopologicalSpace`/`T2Space (V ⧸ L)` — **for every `L`**, no discreteness needed
  (§3, the T2-via-closure trick, spiked).
* `ChartedSpace V (V ⧸ L)` / `IsManifold 𝓘(ℂ, V) ω (V ⧸ L)` — needs `[DiscreteTopology L]` (§4).
  Charts are **raw representative** charts: `chartAt' L x` sends a class near `x` to its unique
  representative in a fixed injectivity ball around `x` (a simplification of the design's
  "centered" charts — the transition maps are still exactly translations by a locally-constant
  lattice element, which is all that is needed; no recentering bookkeeping required).
* `LieAddGroup 𝓘(ℂ, V) ω (V ⧸ L)` — same hypothesis (§5): in the raw charts, addition/negation
  read as translation by a (possibly nonzero, but always locally-constant) lattice element, hence
  affine, hence analytic.
* `CompactSpace (V ⧸ L)` — needs the full `IsZLattice ℝ L` (§6, the
  `IsZLattice.isCompact_range_of_periodic` trick, spiked).
* The `→ₜ+` functoriality substrate `inducedHom` (§9.2, spiked) and its `ContMDiff`-ness (§9.3).

These are genuine theorems/instances *gated* by typeclass hypotheses (`[DiscreteTopology L]`,
`[IsZLattice ℝ L]`); Lean cannot discharge these hypotheses for an arbitrary `L`, so they only
fire once a caller supplies them — which is exactly the hook period-lattice-rank uses once it
establishes discreteness/full-rank for the actual period subgroup.
-/

@[expose] public section

open scoped ContDiff Manifold Pointwise
open Set Filter Topology Metric

noncomputable section

namespace RS

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-! ## §3. Free instances: `AddCommGroup`/`TopologicalSpace`/`T2Space`, no hypotheses at all -/

section T2

variable (L : AddSubgroup V)

instance instAddCommGroupQuotient : AddCommGroup (V ⧸ L) := by infer_instance

instance instTopologicalSpaceQuotient : TopologicalSpace (V ⧸ L) := by infer_instance

end T2

/-! ## §4.1. Uniform injectivity radius -/

section InjRadius

variable (L : AddSubgroup V) [DiscreteTopology L]

omit [NormedSpace ℂ V] in
/-- Every discrete additive subgroup of a normed space has a uniform injectivity radius: some
`ρ > 0` such that every nonzero element has norm at least `2ρ`.
@isnad1 id=ex.0h2v.s7.1b8c6ced7790 from=translated src=- shape=d46373f6 vocab=6d83d746
-/
theorem exists_uniform_injRadius :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ℓ ∈ L, ℓ ≠ 0 → 2 * ρ ≤ ‖ℓ‖ := by
  have h0 : ({(0 : L)} : Set L) ∈ 𝓝 (0 : L) := mem_nhds_discrete.mpr rfl
  rw [nhds_subtype_eq_comap, Filter.mem_comap] at h0
  obtain ⟨U, hU, hUsub⟩ := h0
  obtain ⟨r, hr, hballU⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨r / 2, by linarith, ?_⟩
  intro ℓ hℓL hℓne
  by_contra hlt
  push Not at hlt
  have hballmem : (ℓ : V) ∈ ball (0 : V) r := by
    rw [mem_ball, dist_eq_norm, sub_zero]
    linarith
  have hmem : (⟨ℓ, hℓL⟩ : L) ∈ (Subtype.val : L → V) ⁻¹' U := hballU hballmem
  have h0' := hUsub hmem
  exact hℓne (by simpa using h0')

/-- A choice of uniform injectivity radius for `L`. -/
def injRadius : ℝ := (exists_uniform_injRadius L).choose

omit [NormedSpace ℂ V] in
/--
@isnad1 id=lt.0h2v.s6.ea04038f44e7 from=translated src=- shape=f44967e4 vocab=1721978e
-/
theorem injRadius_pos : 0 < injRadius L := (exists_uniform_injRadius L).choose_spec.1

omit [NormedSpace ℂ V] in
/--
@isnad1 id=le.2h3v.s7.0006c8306985 from=translated src=- shape=3f6181e8 vocab=011e2c9d
-/
theorem norm_le_of_mem_injRadius {ℓ : V} (hℓ : ℓ ∈ L) (hne : ℓ ≠ 0) :
    2 * injRadius L ≤ ‖ℓ‖ := (exists_uniform_injRadius L).choose_spec.2 ℓ hℓ hne

omit [NormedSpace ℂ V] in
/-- `QuotientAddGroup.mk` is injective on any ball of radius `injRadius L`.
@isnad1 id=injon.0h3v.s7.5430e1fd1f3a from=translated src=- shape=bdd38379 vocab=1dcd5a9e
-/
theorem mk_injOn_ball (x : V) :
    Set.InjOn (QuotientAddGroup.mk (s := L)) (ball x (injRadius L)) := by
  intro z₁ hz₁ z₂ hz₂ heq
  have hsub : z₁ - z₂ ∈ L := (QuotientAddGroup.eq_iff_sub_mem).mp heq
  by_contra hne
  have hne' : z₁ - z₂ ≠ 0 := sub_ne_zero.mpr hne
  have h2ρ : 2 * injRadius L ≤ ‖z₁ - z₂‖ := norm_le_of_mem_injRadius L hsub hne'
  have htri : ‖z₁ - z₂‖ < 2 * injRadius L := by
    have h1 : ‖z₁ - x‖ < injRadius L := by rwa [mem_ball, dist_eq_norm] at hz₁
    have h2 : ‖x - z₂‖ < injRadius L := by
      rw [mem_ball, dist_eq_norm] at hz₂
      rwa [norm_sub_rev]
    calc ‖z₁ - z₂‖ = ‖(z₁ - x) + (x - z₂)‖ :=
        by rw [show (z₁ - x) + (x - z₂) = z₁ - z₂ from by abel]
      _ ≤ ‖z₁ - x‖ + ‖x - z₂‖ := norm_add_le _ _
      _ < injRadius L + injRadius L := add_lt_add h1 h2
      _ = 2 * injRadius L := by ring
  linarith

end InjRadius

/-! ## §4.2. The raw representative chart family -/

section Chart

variable (L : AddSubgroup V) [DiscreteTopology L]

/-- The auxiliary chart going `V → V ⧸ L`: `mk` restricted to the injectivity ball around `x`,
which is a continuous open injection, hence (by `ofContinuousOpen`) an `OpenPartialHomeomorph`. -/
def rawChartAux (x : V) : OpenPartialHomeomorph V (V ⧸ L) :=
  OpenPartialHomeomorph.ofContinuousOpen
    ((mk_injOn_ball L x).toPartialEquiv (QuotientAddGroup.mk (s := L)) (ball x (injRadius L)))
    (QuotientAddGroup.continuous_mk).continuousOn
    (QuotientAddGroup.isOpenMap_coe)
    Metric.isOpen_ball

omit [NormedSpace ℂ V] in
/--
@isnad1 id=eq.0h4v.s7.730e3225ed91 from=translated src=- shape=95b80aa9 vocab=67d15404
-/
@[simp] theorem rawChartAux_apply (x z : V) : rawChartAux L x z = QuotientAddGroup.mk z := rfl

omit [NormedSpace ℂ V] in
/--
@isnad1 id=eq.0h3v.s7.f96ed9d98510 from=translated src=- shape=e1e156d5 vocab=e07cff9a
-/
@[simp] theorem rawChartAux_source (x : V) : (rawChartAux L x).source = ball x (injRadius L) := rfl

/-- The chart at representative `x : V`: sends a class near `x` to its unique representative in
`ball x (injRadius L)`. -/
def chartAt' (x : V) : OpenPartialHomeomorph (V ⧸ L) V := (rawChartAux L x).symm

omit [NormedSpace ℂ V] in
/--
@isnad1 id=eq.0h3v.s7.159c7c70b350 from=translated src=- shape=8a33a035 vocab=61f2db11
-/
@[simp] theorem chartAt'_symm (x : V) : (chartAt' L x).symm = rawChartAux L x := rfl

omit [NormedSpace ℂ V] in
/--
@isnad1 id=eq.0h3v.s7.dadb404045f9 from=translated src=- shape=f5e9b0ec vocab=cf996779
-/
@[simp] theorem chartAt'_source (x : V) :
    (chartAt' L x).source = QuotientAddGroup.mk '' ball x (injRadius L) := rfl

omit [NormedSpace ℂ V] in
/--
@isnad1 id=eq.0h3v.s7.923937982564 from=translated src=- shape=3b0fbc6d vocab=18cc172b
-/
@[simp] theorem chartAt'_target (x : V) : (chartAt' L x).target = ball x (injRadius L) := rfl

omit [NormedSpace ℂ V] in
/-- The defining property of `chartAt'`: on a representative `z` inside the ball, the chart
recovers `z`.
@isnad1 id=eq.1h4v.s7.a72088e6b751 from=translated src=- shape=59d7cb38 vocab=c6c862ed
-/
theorem chartAt'_apply_mk {x z : V} (hz : z ∈ ball x (injRadius L)) :
    chartAt' L x (QuotientAddGroup.mk z) = z :=
  (rawChartAux L x).left_inv hz

omit [NormedSpace ℂ V] in
/-- If `w + ℓ` lands in the ball around `x'` for some `ℓ ∈ L`, the chart at `x'` reads the class
of `w` as `w + ℓ`. This is the single computation underlying every transition/smoothness proof
below.
@isnad1 id=eq.2h5v.s7.7a47eea0f599 from=translated src=- shape=9364ccaa vocab=41235607
-/
theorem chartAt'_eq_add_of_mem_ball {x' w ℓ : V} (hℓ : ℓ ∈ L)
    (hmem : w + ℓ ∈ ball x' (injRadius L)) :
    chartAt' L x' (QuotientAddGroup.mk w) = w + ℓ := by
  have hmk : (QuotientAddGroup.mk (w + ℓ) : V ⧸ L) = QuotientAddGroup.mk w := by
    rw [QuotientAddGroup.eq_iff_sub_mem]
    simpa using (AddSubgroup.neg_mem L hℓ)
  rw [← hmk]
  exact chartAt'_apply_mk L hmem

omit [NormedSpace ℂ V] in
/-- Local constancy: the identity `chartAt' L x' (mk w) = w + ℓ` persists on a whole neighborhood
of `w`, for the *same* `ℓ`.
@isnad1 id=eventual.2h5v.s7.01a21a552017 from=translated src=- shape=4d60de8b vocab=9adbf9ab
-/
theorem chartAt'_eventuallyEq_add {x' w ℓ : V} (hℓ : ℓ ∈ L)
    (hmem : w + ℓ ∈ ball x' (injRadius L)) :
    (fun w => chartAt' L x' (QuotientAddGroup.mk w)) =ᶠ[𝓝 w] (fun w => w + ℓ) := by
  obtain ⟨ε, hε, hballsub⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball (w + ℓ) hmem
  filter_upwards [Metric.ball_mem_nhds w hε] with w' hw'
  apply chartAt'_eq_add_of_mem_ball L hℓ
  apply hballsub
  rw [mem_ball, dist_eq_norm] at hw' ⊢
  simpa [add_sub_add_right_eq_sub] using hw'

omit [NormedSpace ℂ V] in
/--
@isnad1 id=mem.0h3v.s8.5352b946f241 from=translated src=- shape=47a19e79 vocab=93244b26
-/
theorem chartAt'_mem_source (q : V ⧸ L) :
    q ∈ (chartAt' L (Function.surjInv QuotientAddGroup.mk_surjective q)).source := by
  set x := Function.surjInv QuotientAddGroup.mk_surjective q with hx_def
  have hxq : (QuotientAddGroup.mk x : V ⧸ L) = q := Function.surjInv_eq _ q
  rw [chartAt'_source]
  exact ⟨x, Metric.mem_ball_self (injRadius_pos L), hxq⟩

/-- `ChartedSpace V (V ⧸ L)`, given a discrete additive subgroup `L`. -/
instance instChartedSpace : ChartedSpace V (V ⧸ L) :=
  chartedSpaceOfFamily' (chartAt' L) (fun q => Function.surjInv QuotientAddGroup.mk_surjective q)
    (chartAt'_mem_source L)

omit [NormedSpace ℂ V] in
/--
@isnad1 id=eq.0h3v.s7.c2c39955d6a1 from=translated src=- shape=2009e785 vocab=86260520
-/
@[simp] theorem chartAt_eq (q : V ⧸ L) :
    chartAt V q = chartAt' L (Function.surjInv QuotientAddGroup.mk_surjective q) := rfl

/-- The canonical chart at `q`, evaluated at any point, agrees with `chartAt'` at the same
representative.
@isnad1 id=eq.0h4v.s8.3b9e4a23dfe2 from=translated src=- shape=e3c333eb vocab=9fa754b4
-/
theorem extChartAt_apply_eq (q q' : V ⧸ L) :
    extChartAt 𝓘(ℂ, V) q q' = chartAt' L (Function.surjInv QuotientAddGroup.mk_surjective q) q' :=
        by
  rw [extChartAt_coe, Function.comp_apply, modelWithCornersSelf_coe, id_eq, chartAt_eq]

/--
@isnad1 id=eq.0h4v.s7.83074503d6cb from=translated src=- shape=eab161c1 vocab=d1323de1
-/
theorem extChartAt_symm_apply_eq (q : V ⧸ L) (w : V) :
    (extChartAt 𝓘(ℂ, V) q).symm w = QuotientAddGroup.mk w := by
  rw [extChartAt_coe_symm, Function.comp_apply, modelWithCornersSelf_coe_symm, id_eq, chartAt_eq]
  rfl

/--
@isnad1 id=eq.0h3v.s7.66b05899c4c6 from=translated src=- shape=e5ea285d vocab=f5670364
-/
theorem extChartAt_self_eq (q : V ⧸ L) :
    extChartAt 𝓘(ℂ, V) q q = Function.surjInv QuotientAddGroup.mk_surjective q := by
  rw [extChartAt_apply_eq]
  set x := Function.surjInv QuotientAddGroup.mk_surjective q
  have hxq : (QuotientAddGroup.mk x : V ⧸ L) = q := Function.surjInv_eq _ q
  nth_rewrite 1 [← hxq]
  exact chartAt'_apply_mk L (Metric.mem_ball_self (injRadius_pos L))

end Chart

/-! ## §4.3. `IsManifold`: transitions are translations by a locally-constant lattice element -/

section Manifold

variable (L : AddSubgroup V) [DiscreteTopology L]

/-- The transition map between two raw representative charts is analytic on its whole source
(translation by a locally-constant lattice element). Exposed standalone (not just inside the
`IsManifold` instance) so the `ULift` transport toolkit can reuse it verbatim.
@isnad1 id=analytic.0h4v.s8.cb9d7726fff5 from=translated src=- shape=cb55562b vocab=d4afa67a
-/
theorem analyticOnNhd_chartAt'_trans (x x' : V) :
    AnalyticOnNhd ℂ ((chartAt' L x).symm ≫ₕ chartAt' L x')
      ((chartAt' L x).symm ≫ₕ chartAt' L x').source := by
  intro w hw
  rw [OpenPartialHomeomorph.trans_source] at hw
  obtain ⟨hw1, hw2⟩ := hw
  rw [chartAt'_symm, rawChartAux_source] at hw1
  rw [chartAt'_symm, Set.mem_preimage, rawChartAux_apply, chartAt'_source] at hw2
  obtain ⟨z', hz', hzeq⟩ := hw2
  set ℓ := z' - w with hℓ_def
  have hℓL : ℓ ∈ L := by
    have := (QuotientAddGroup.eq_iff_sub_mem (x := z') (y := w)).mp hzeq
    simpa [hℓ_def] using this
  have hmem : w + ℓ ∈ ball x' (injRadius L) := by
    have hzw : w + ℓ = z' := by rw [hℓ_def]; abel
    rwa [hzw]
  have heq : (chartAt' L x).symm ≫ₕ chartAt' L x' =ᶠ[𝓝 w] (fun w => w + ℓ) := by
    filter_upwards [chartAt'_eventuallyEq_add L hℓL hmem] with w' hw'
    rw [OpenPartialHomeomorph.trans_apply, chartAt'_symm, rawChartAux_apply]
    exact hw'
  exact (analyticAt_id.add analyticAt_const).congr heq.symm

end Manifold

/-! ## §5. `LieAddGroup`: addition/negation are affine in the raw charts -/

section LieGroupAux

variable (L : AddSubgroup V) [DiscreteTopology L] [CompleteSpace V]

omit [NormedSpace ℂ V] [DiscreteTopology ↥L] [CompleteSpace V] in
/--
@isnad1 id=continuo.0h2v.s8.3412c3120b88 from=translated src=- shape=4e3edb54 vocab=6d99d93d
-/
theorem continuous_add_torus : Continuous (fun p : (V ⧸ L) × (V ⧸ L) => p.1 + p.2) := by
  have : IsTopologicalAddGroup (V ⧸ L) := QuotientAddGroup.instIsTopologicalAddGroup L
  fun_prop

omit [NormedSpace ℂ V] [DiscreteTopology ↥L] [CompleteSpace V] in
/--
@isnad1 id=continuo.0h2v.s7.8d12273c1320 from=translated src=- shape=5f1bc6ab vocab=d275c0f0
-/
theorem continuous_neg_torus : Continuous (fun q : V ⧸ L => -q) := by
  have : IsTopologicalAddGroup (V ⧸ L) := QuotientAddGroup.instIsTopologicalAddGroup L
  fun_prop

/-- Addition on the torus is `ω`-smooth: in aligned raw charts (codomain chart representative
chosen at a fixed lattice offset from the sum of the domain representatives), the chart composite
is affine.
@isnad1 id=contmdif.0h2v.s9.4a0d655f32fb from=translated src=- shape=16d5336c vocab=55829703
-/
theorem contMDiff_add_torus :
    ContMDiff (𝓘(ℂ, V).prod 𝓘(ℂ, V)) 𝓘(ℂ, V) ω (fun p : (V ⧸ L) × (V ⧸ L) => p.1 + p.2) := by
  rintro ⟨q₁, q₂⟩
  set x₁ := Function.surjInv QuotientAddGroup.mk_surjective q₁ with hx₁_def
  set x₂ := Function.surjInv QuotientAddGroup.mk_surjective q₂ with hx₂_def
  set x₃ := Function.surjInv QuotientAddGroup.mk_surjective (q₁ + q₂) with hx₃_def
  have hx₁q : (QuotientAddGroup.mk x₁ : V ⧸ L) = q₁ := Function.surjInv_eq _ q₁
  have hx₂q : (QuotientAddGroup.mk x₂ : V ⧸ L) = q₂ := Function.surjInv_eq _ q₂
  have hx₃q : (QuotientAddGroup.mk x₃ : V ⧸ L) = q₁ + q₂ := Function.surjInv_eq _ (q₁ + q₂)
  have hsum : (QuotientAddGroup.mk (x₁ + x₂) : V ⧸ L) = q₁ + q₂ := by
    rw [QuotientAddGroup.mk_add, hx₁q, hx₂q]
  set ℓ := x₃ - (x₁ + x₂) with hℓ_def
  have hℓL' : ℓ ∈ L := by
    have heq : (QuotientAddGroup.mk x₃ : V ⧸ L) = QuotientAddGroup.mk (x₁ + x₂) := by
      rw [hx₃q, hsum]
    have := (QuotientAddGroup.eq_iff_sub_mem).mp heq
    simpa [hℓ_def] using this
  rw [contMDiffAt_iff]
  refine ⟨(continuous_add_torus L).continuousAt, ?_⟩
  rw [ModelWithCorners.range_prod, modelWithCornersSelf_coe, Set.range_id, Set.univ_prod_univ,
    contDiffWithinAt_univ]
  have hpt : extChartAt (𝓘(ℂ, V).prod 𝓘(ℂ, V)) (q₁, q₂) (q₁, q₂) = (x₁, x₂) := by
    rw [extChartAt_prod]
    change (extChartAt 𝓘(ℂ, V) q₁ q₁, extChartAt 𝓘(ℂ, V) q₂ q₂) = (x₁, x₂)
    rw [extChartAt_self_eq L q₁, extChartAt_self_eq L q₂]
  rw [hpt]
  have hexact : ∀ p : V × V, extChartAt 𝓘(ℂ, V) (q₁ + q₂)
      ((fun p : (V ⧸ L) × (V ⧸ L) => p.1 + p.2)
        ((extChartAt (𝓘(ℂ, V).prod 𝓘(ℂ, V)) (q₁, q₂)).symm p))
      = chartAt' L x₃ (QuotientAddGroup.mk (p.1 + p.2)) := by
    intro p
    rw [extChartAt_apply_eq]
    have hsymm : (extChartAt (𝓘(ℂ, V).prod 𝓘(ℂ, V)) (q₁, q₂)).symm p
        = (QuotientAddGroup.mk p.1, QuotientAddGroup.mk p.2) := by
      rw [extChartAt_prod, PartialEquiv.prod_symm, PartialEquiv.prod_coe]
      change ((extChartAt 𝓘(ℂ, V) q₁).symm p.1, (extChartAt 𝓘(ℂ, V) q₂).symm p.2)
        = (QuotientAddGroup.mk p.1, QuotientAddGroup.mk p.2)
      rw [extChartAt_symm_apply_eq, extChartAt_symm_apply_eq]
    rw [hsymm]
    change chartAt' L x₃ (QuotientAddGroup.mk p.1 + QuotientAddGroup.mk p.2)
      = chartAt' L x₃ (QuotientAddGroup.mk (p.1 + p.2))
    rw [QuotientAddGroup.mk_add]
  have hAnalytic : AnalyticAt ℂ (fun p : V × V => p.1 + p.2 + ℓ) (x₁, x₂) :=
    (analyticAt_fst.add analyticAt_snd).add analyticAt_const
  have hmemball : x₁ + x₂ + ℓ ∈ ball x₃ (injRadius L) := by
    have hval : x₁ + x₂ + ℓ = x₃ := by rw [hℓ_def]; abel
    rw [hval]
    exact Metric.mem_ball_self (injRadius_pos L)
  have hEv : (fun w => chartAt' L x₃ (QuotientAddGroup.mk w)) =ᶠ[𝓝 (x₁ + x₂)]
      (fun w => w + ℓ) := chartAt'_eventuallyEq_add L hℓL' hmemball
  have hcont : Tendsto (fun p : V × V => p.1 + p.2) (𝓝 (x₁, x₂)) (𝓝 (x₁ + x₂)) :=
    (continuous_add).tendsto (x₁, x₂)
  have hgoal_eq : (fun p : V × V => extChartAt 𝓘(ℂ, V) (q₁ + q₂)
      ((fun p : (V ⧸ L) × (V ⧸ L) => p.1 + p.2)
        ((extChartAt (𝓘(ℂ, V).prod 𝓘(ℂ, V)) (q₁, q₂)).symm p)))
      =ᶠ[𝓝 (x₁, x₂)] (fun p : V × V => p.1 + p.2 + ℓ) := by
    filter_upwards [hcont.eventually hEv] with p hp
    rw [hexact p]
    exact hp
  exact (hAnalytic.congr hgoal_eq.symm).contDiffAt

/-- Negation on the torus is `ω`-smooth: same affine-chart-composite argument as addition.
@isnad1 id=contmdif.0h2v.s8.547737376d82 from=translated src=- shape=1fd68609 vocab=cbd81876
-/
theorem contMDiff_neg_torus : ContMDiff 𝓘(ℂ, V) 𝓘(ℂ, V) ω (fun q : V ⧸ L => -q) := by
  intro q
  set x := Function.surjInv QuotientAddGroup.mk_surjective q with hx_def
  set x' := Function.surjInv QuotientAddGroup.mk_surjective (-q) with hx'_def
  have hxq : (QuotientAddGroup.mk x : V ⧸ L) = q := Function.surjInv_eq _ q
  have hx'q : (QuotientAddGroup.mk x' : V ⧸ L) = -q := Function.surjInv_eq _ (-q)
  set ℓ := x' - -x with hℓ_def
  have hℓL : ℓ ∈ L := by
    have heq : (QuotientAddGroup.mk x' : V ⧸ L) = QuotientAddGroup.mk (-x) := by
      rw [hx'q, QuotientAddGroup.mk_neg, hxq]
    have := (QuotientAddGroup.eq_iff_sub_mem).mp heq
    simpa [hℓ_def] using this
  rw [contMDiffAt_iff]
  refine ⟨(continuous_neg_torus L).continuousAt, ?_⟩
  rw [modelWithCornersSelf_coe, Set.range_id, contDiffWithinAt_univ]
  have hpt : extChartAt 𝓘(ℂ, V) q q = x := extChartAt_self_eq L q
  rw [hpt]
  have hexact : ∀ w : V, extChartAt 𝓘(ℂ, V) (-q) (-(extChartAt 𝓘(ℂ, V) q).symm w)
      = chartAt' L x' (QuotientAddGroup.mk (-w)) := by
    intro w
    rw [extChartAt_symm_apply_eq, QuotientAddGroup.mk_neg, extChartAt_apply_eq]
  have hAnalytic : AnalyticAt ℂ (fun w : V => -w + ℓ) x :=
    (analyticAt_id.neg).add analyticAt_const
  have hmemball : -x + ℓ ∈ ball x' (injRadius L) := by
    have hval : -x + ℓ = x' := by rw [hℓ_def]; abel
    rw [hval]
    exact Metric.mem_ball_self (injRadius_pos L)
  have hEv : (fun w => chartAt' L x' (QuotientAddGroup.mk w)) =ᶠ[𝓝 (-x)]
      (fun w => w + ℓ) := chartAt'_eventuallyEq_add L hℓL hmemball
  have hcont : Tendsto (fun w : V => -w) (𝓝 x) (𝓝 (-x)) := continuous_neg.tendsto x
  have hgoal_eq : (fun w : V => extChartAt 𝓘(ℂ, V) (-q) (-(extChartAt 𝓘(ℂ, V) q).symm w))
      =ᶠ[𝓝 x] (fun w : V => -w + ℓ) := by
    filter_upwards [hcont.eventually hEv] with w hw
    rw [hexact w]
    exact hw
  exact (hAnalytic.congr hgoal_eq.symm).contDiffAt

end LieGroupAux

/-! ## §6. `CompactSpace`, given the full-rank hypothesis -/

section Compact

variable (L : Submodule ℤ V) [DiscreteTopology L]

end Compact

/-! ## §9. The `→ₜ+` functoriality substrate -/

section InducedHom

variable {V' : Type*} [NormedAddCommGroup V'] [NormedSpace ℂ V'] [CompleteSpace V']
  [FiniteDimensional ℂ V] [FiniteDimensional ℂ V']

/-- The `→ₜ+` functoriality substrate: a `ℂ`-linear map `T : V →ₗ[ℂ] V'` with `L ≤ L'.comap T`
induces a continuous additive homomorphism on the quotients. -/
def inducedHom (L : AddSubgroup V) (L' : AddSubgroup V') (T : V →ₗ[ℂ] V')
    (hT : L ≤ L'.comap T.toAddMonoidHom) : (V ⧸ L) →ₜ+ (V' ⧸ L') :=
  { QuotientAddGroup.map L L' T.toAddMonoidHom hT with
    continuous_toFun := by
      change Continuous (⇑(QuotientAddGroup.map L L' T.toAddMonoidHom hT))
      rw [(QuotientAddGroup.isQuotientMap_mk (N := L)).continuous_iff]
      have heq : (⇑(QuotientAddGroup.map L L' T.toAddMonoidHom hT)) ∘ QuotientAddGroup.mk =
          QuotientAddGroup.mk ∘ T :=
        funext fun x => QuotientAddGroup.map_mk L L' T.toAddMonoidHom hT x
      rw [heq]
      exact QuotientAddGroup.continuous_mk.comp T.continuous_of_finiteDimensional }

omit [CompleteSpace V'] [FiniteDimensional ℂ V'] in
/--
@isnad1 id=eq.1h6v.s9.f70bfe7d5daf from=translated src=- shape=b60f73e1 vocab=41b49537
-/
@[simp] theorem inducedHom_apply_mk {L : AddSubgroup V} {L' : AddSubgroup V'}
    {T : V →ₗ[ℂ] V'} (hT : L ≤ L'.comap T.toAddMonoidHom) (x : V) :
    inducedHom L L' T hT (QuotientAddGroup.mk x) = QuotientAddGroup.mk (T x) :=
  QuotientAddGroup.map_mk L L' T.toAddMonoidHom hT x

omit [CompleteSpace V'] [FiniteDimensional ℂ V'] in
/-- Any `ℂ`-linear map between finite-dimensional normed spaces is entire (analytic at every
point): it is continuous (finite-dimensional domain), hence bounded, hence its own convergent
power series.
@isnad1 id=analytic.0h4v.s7.8851d79dbbc0 from=translated src=- shape=0c766629 vocab=d13a043b
-/
theorem analyticAt_linearMap (T : V →ₗ[ℂ] V') (x : V) : AnalyticAt ℂ (⇑T) x :=
  (⟨T, T.continuous_of_finiteDimensional⟩ : V →L[ℂ] V').analyticAt x

omit [FiniteDimensional ℂ V'] in
/-- The induced map on tori is `ω`-smooth, given discreteness of both lattices (needed for the
manifold structure on either side; no further hypothesis on `T`/`hT` beyond linearity).
@isnad1 id=contmdif.1h5v.s9.8aa216f93949 from=translated src=- shape=0c8383b8 vocab=a41a815f
-/
theorem contMDiff_inducedHom {L : AddSubgroup V} {L' : AddSubgroup V'}
    [DiscreteTopology L] [DiscreteTopology L']
    {T : V →ₗ[ℂ] V'} (hT : L ≤ L'.comap T.toAddMonoidHom) :
    ContMDiff 𝓘(ℂ, V) 𝓘(ℂ, V') ω (inducedHom L L' T hT) := by
  intro q
  set x := Function.surjInv QuotientAddGroup.mk_surjective q with hx_def
  set y := Function.surjInv QuotientAddGroup.mk_surjective (inducedHom L L' T hT q) with hy_def
  have hxq : (QuotientAddGroup.mk x : V ⧸ L) = q := Function.surjInv_eq _ q
  have hyq : (QuotientAddGroup.mk y : V' ⧸ L') = inducedHom L L' T hT q :=
    Function.surjInv_eq _ _
  set ℓ := y - T x with hℓ_def
  have hℓL' : ℓ ∈ L' := by
    have heq : (QuotientAddGroup.mk y : V' ⧸ L') = QuotientAddGroup.mk (T x) := by
      rw [hyq, ← hxq, inducedHom_apply_mk]
    have := (QuotientAddGroup.eq_iff_sub_mem).mp heq
    simpa [hℓ_def] using this
  rw [contMDiffAt_iff]
  refine ⟨(inducedHom L L' T hT).continuous.continuousAt, ?_⟩
  rw [modelWithCornersSelf_coe, Set.range_id, contDiffWithinAt_univ]
  have hpt : extChartAt 𝓘(ℂ, V) q q = x := extChartAt_self_eq L q
  rw [hpt]
  have hexact : ∀ w : V, extChartAt 𝓘(ℂ, V') (inducedHom L L' T hT q)
      (inducedHom L L' T hT ((extChartAt 𝓘(ℂ, V) q).symm w))
      = chartAt' L' y (QuotientAddGroup.mk (T w)) := by
    intro w
    rw [extChartAt_symm_apply_eq, inducedHom_apply_mk, extChartAt_apply_eq]
  have hAnalytic : AnalyticAt ℂ (fun w : V => T w + ℓ) x :=
    (analyticAt_linearMap T x).add analyticAt_const
  have hmemball : T x + ℓ ∈ ball y (injRadius L') := by
    have hval : T x + ℓ = y := by rw [hℓ_def]; abel
    rw [hval]
    exact Metric.mem_ball_self (injRadius_pos L')
  have hEv : (fun w => chartAt' L' y (QuotientAddGroup.mk w)) =ᶠ[𝓝 (T x)]
      (fun w => w + ℓ) := chartAt'_eventuallyEq_add L' hℓL' hmemball
  have hcont : Tendsto (⇑T) (𝓝 x) (𝓝 (T x)) := T.continuous_of_finiteDimensional.continuousAt
  have hgoal_eq : (fun w : V => extChartAt 𝓘(ℂ, V') (inducedHom L L' T hT q)
      (inducedHom L L' T hT ((extChartAt 𝓘(ℂ, V) q).symm w)))
      =ᶠ[𝓝 x] (fun w : V => T w + ℓ) := by
    filter_upwards [hcont.eventually hEv] with w hw
    rw [hexact w]
    exact hw
  exact (hAnalytic.congr hgoal_eq.symm).contDiffAt

/-! ### Functoriality of `inducedHom` (requested by jacobian-functoriality,
`docs/requests/jacobian-construction.md`) -/

omit [FiniteDimensional ℂ V] in
/-- `inducedHom` at the identity is the identity (`QuotientAddGroup.map` functoriality).
@isnad1 id=eq.1h2v.s8.2eb05948a506 from=translated src=- shape=03017962 vocab=2cb7606c
-/
theorem inducedHom_id [FiniteDimensional ℂ V] (L : AddSubgroup V)
    (hT : L ≤ L.comap (LinearMap.id (R := ℂ) (M := V)).toAddMonoidHom) :
    inducedHom L L LinearMap.id hT = ContinuousAddMonoidHom.id (V ⧸ L) := by
  ext q
  refine QuotientAddGroup.induction_on q fun v => ?_
  change inducedHom L L LinearMap.id hT (QuotientAddGroup.mk v) = QuotientAddGroup.mk v
  rw [inducedHom_apply_mk]
  rfl

omit [CompleteSpace V'] in
/-- `inducedHom` is compositional (`QuotientAddGroup.map` functoriality).
@isnad1 id=eq.3h8v.s9.11ba4e70b466 from=translated src=- shape=ebfc8b63 vocab=924d96ce
-/
theorem inducedHom_comp {V'' : Type*} [NormedAddCommGroup V''] [NormedSpace ℂ V'']
    (L : AddSubgroup V) (L' : AddSubgroup V') (L'' : AddSubgroup V'')
    (T : V →ₗ[ℂ] V') (T' : V' →ₗ[ℂ] V'')
    (hT : L ≤ L'.comap T.toAddMonoidHom) (hT' : L' ≤ L''.comap T'.toAddMonoidHom)
    (hTT' : L ≤ L''.comap (T'.comp T).toAddMonoidHom) :
    (inducedHom L' L'' T' hT').comp (inducedHom L L' T hT)
      = inducedHom L L'' (T'.comp T) hTT' := by
  ext q
  refine QuotientAddGroup.induction_on q fun v => ?_
  change inducedHom L' L'' T' hT' (inducedHom L L' T hT (QuotientAddGroup.mk v))
    = inducedHom L L'' (T'.comp T) hTT' (QuotientAddGroup.mk v)
  rw [inducedHom_apply_mk, inducedHom_apply_mk, inducedHom_apply_mk]
  rfl

end InducedHom

end RS
