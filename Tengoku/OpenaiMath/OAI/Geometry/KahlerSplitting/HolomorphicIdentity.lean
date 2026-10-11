import Tengoku.OpenaiMath.OAI.Geometry.KahlerSplitting.ProductCharts

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open scoped ENNReal NNReal
open scoped Manifold ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open scoped Manifold ENNReal
open Set Metric Filter Topology Asymptotics
open Set MeasureTheory
open Set Metric Filter Topology MeasureTheory
open scoped Interval
open Set Filter Topology Metric Complex
open Set Filter Topology Metric
open Set Metric Filter Topology
open scoped ContDiff
open Set
open scoped Manifold ContDiff
open Set Metric
open Set Filter Topology
open scoped Manifold

namespace UniversalCoverSplitting
section ComplexIdentity
open Filter Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem holomorphic_eqOn_of_convex_of_eventuallyEq
    {U : Set E} (hU : IsOpen U) (hc : Convex ℝ U) {f g : E → F}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    {x : E} (hx : x ∈ U) (hfg : f =ᶠ[𝓝 x] g) : EqOn f g U := by
  intro y hy
  let l : ℂ →ᴬ[ℂ] E := ContinuousAffineMap.lineMap x y
  let L : ℂ →L[ℝ] E := ((ContinuousLinearMap.id ℂ ℂ).smulRight (y - x)).restrictScalars ℝ
  have he : ∀ z : ℂ, l z = L z + x := fun z ↦ rfl
  have hl0 : l 0 = x := by simp [l, ContinuousAffineMap.coe_lineMap_eq]
  have hl1 : l 1 = y := by simp [l, ContinuousAffineMap.coe_lineMap_eq]
  have hopen : IsOpen (l ⁻¹' U) := hU.preimage l.continuous
  have hconv : Convex ℝ (l ⁻¹' U) := by
    change Convex ℝ ((fun z ↦ L z + x) ⁻¹' U)
    exact (hc.translate_preimage_left x).linear_preimage L.toLinearMap
  have hf' : DifferentiableOn ℂ (f ∘ l) (l ⁻¹' U) :=
    hf.comp l.differentiableOn (mapsTo_preimage _ _)
  have hg' : DifferentiableOn ℂ (g ∘ l) (l ⁻¹' U) :=
    hg.comp l.differentiableOn (mapsTo_preimage _ _)
  have hlocal : (f ∘ l) =ᶠ[𝓝 0] (g ∘ l) :=
    hfg.comp_tendsto (hl0 ▸ l.continuous.continuousAt)
  have hzero : (0 : ℂ) ∈ l ⁻¹' U := by simpa only [mem_preimage, hl0] using hx
  have hone : (1 : ℂ) ∈ l ⁻¹' U := by simpa only [mem_preimage, hl1] using hy
  have h := (hf'.analyticOnNhd hopen).eqOn_of_preconnected_of_eventuallyEq
    (hg'.analyticOnNhd hopen) hconv.isPreconnected hzero hlocal hone
  simpa only [Function.comp_apply, hl1] using h

theorem holomorphic_eqOn_of_preconnected_of_eventuallyEq
    {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U) {f g : E → F}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    {x : E} (hx : x ∈ U) (hfg : f =ᶠ[𝓝 x] g) : EqOn f g U := by
  let V := {z : E | f =ᶠ[𝓝 z] g}
  have hV : IsOpen V := isOpen_setOfPred_eventually_nhds
  have hVU : U ⊆ V := by
    refine hc.subset_of_closure_inter_subset hV ⟨x, hx, hfg⟩ ?_
    intro z hz
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU z hz.2
    obtain ⟨w, hwB, hwV⟩ := mem_closure_iff.mp hz.1 (Metric.ball z r)
      Metric.isOpen_ball (Metric.mem_ball_self hr)
    have heq : EqOn f g (Metric.ball z r) :=
      holomorphic_eqOn_of_convex_of_eventuallyEq Metric.isOpen_ball (convex_ball z r)
        (hf.mono hrU) (hg.mono hrU) hwB hwV
    exact Filter.mem_of_superset (Metric.ball_mem_nhds z hr) heq
  intro z hz
  exact (hVU hz).eq_of_nhds

end ComplexIdentity
end UniversalCoverSplitting

namespace UniversalCoverSplitting
section ManifoldIdentity
open Filter Topology
open scoped Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {n : ℕ} {X : ComplexManifold n}

theorem holomorphic_manifold_eqOn_of_preconnected_of_eventuallyEq
    {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U) {f g : E → X.Carrier}
    (hf : MDifferentiableOn 𝓘(ℂ, E) (model n) f U)
    (hg : MDifferentiableOn 𝓘(ℂ, E) (model n) g U)
    {x : E} (hx : x ∈ U) (hfg : f =ᶠ[𝓝 x] g) : EqOn f g U := by
  let V := {z : E | f =ᶠ[𝓝 z] g}
  have hV : IsOpen V := isOpen_setOfPred_eventually_nhds
  have hVU : U ⊆ V := by
    refine hc.subset_of_closure_inter_subset hV ⟨x, hx, hfg⟩ ?_
    intro z hz
    have hcf : ContinuousAt f z := (hf.mdifferentiableAt (hU.mem_nhds hz.2)).continuousAt
    have hcg : ContinuousAt g z := (hg.mdifferentiableAt (hU.mem_nhds hz.2)).continuousAt
    have : (𝓝[V] z).NeBot := mem_closure_iff_clusterPt.mp hz.1
    have heq : f z = g z := tendsto_nhds_unique_of_eventuallyEq
      hcf.continuousWithinAt hcg.continuousWithinAt
      (Filter.mem_of_superset self_mem_nhdsWithin fun w (hw : w ∈ V) ↦ hw.eq_of_nhds)
    let c := extChartAt (model n) (f z)
    have hsrc : c.source ∈ 𝓝 (f z) := extChartAt_source_mem_nhds (I := model n) (f z)
    have hN : U ∩ (f ⁻¹' c.source ∩ g ⁻¹' c.source) ∈ 𝓝 z :=
      inter_mem (hU.mem_nhds hz.2) (inter_mem (hcf hsrc) (hcg (heq ▸ hsrc)))
    obtain ⟨r, hr, hrN⟩ := Metric.mem_nhds_iff.mp hN
    have hfc : DifferentiableOn ℂ (c ∘ f) (Metric.ball z r) := by
      intro a ha
      have hm : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, Model n) (c ∘ f) a :=
        (mdifferentiableAt_extChartAt (I := model n) (by
          simpa only [mem_preimage, c, extChartAt_source] using (hrN ha).2.1)).comp a
          (hf.mdifferentiableAt (hU.mem_nhds (hrN ha).1))
      exact hm.differentiableAt.differentiableWithinAt
    have hgc : DifferentiableOn ℂ (c ∘ g) (Metric.ball z r) := by
      intro a ha
      have hm : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, Model n) (c ∘ g) a :=
        (mdifferentiableAt_extChartAt (I := model n) (by
          simpa only [mem_preimage, c, extChartAt_source] using (hrN ha).2.2)).comp a
          (hg.mdifferentiableAt (hU.mem_nhds (hrN ha).1))
      exact hm.differentiableAt.differentiableWithinAt
    obtain ⟨w, hwB, hwV⟩ := mem_closure_iff.mp hz.1 (Metric.ball z r)
      Metric.isOpen_ball (Metric.mem_ball_self hr)
    have hchart : EqOn (c ∘ f) (c ∘ g) (Metric.ball z r) :=
      holomorphic_eqOn_of_convex_of_eventuallyEq Metric.isOpen_ball (convex_ball z r)
        hfc hgc hwB (hwV.mono fun a ha ↦ congrArg c ha)
    exact Filter.mem_of_superset (Metric.ball_mem_nhds z hr) fun a ha ↦
      c.injOn (hrN ha).2.1 (hrN ha).2.2 (hchart ha)
  intro z hz
  exact (hVU hz).eq_of_nhds

end ManifoldIdentity
end UniversalCoverSplitting

namespace UniversalCoverSplitting
section ManifoldSourceIdentity
open Filter Topology
open scoped Manifold
variable {m n : ℕ} {M : ComplexManifold m} {X : ComplexManifold n}

theorem holomorphic_manifolds_eqOn_of_preconnected_of_eventuallyEq
    {U : Set M.Carrier} (hU : IsOpen U) (hc : IsPreconnected U)
    {f g : M.Carrier → X.Carrier}
    (hf : MDifferentiableOn (model m) (model n) f U)
    (hg : MDifferentiableOn (model m) (model n) g U)
    {x : M.Carrier} (hx : x ∈ U) (hfg : f =ᶠ[𝓝 x] g) : EqOn f g U := by
  let V := {z : M.Carrier | f =ᶠ[𝓝 z] g}
  have hV : IsOpen V := isOpen_setOfPred_eventually_nhds
  have hVU : U ⊆ V := by
    refine hc.subset_of_closure_inter_subset hV ⟨x, hx, hfg⟩ ?_
    intro z hz
    let e := chartAt (Model m) z
    have hzs : z ∈ e.source := mem_chart_source _ _
    have hzt : e z ∈ e.target := e.map_source hzs
    have hcz : ContinuousAt e z := e.continuousAt hzs
    have hcs : ContinuousAt e.symm (e z) := e.symm.continuousAt hzt
    have hN : e.target ∩ e.symm ⁻¹' U ∈ 𝓝 (e z) := by
      refine inter_mem (e.open_target.mem_nhds hzt) (hcs ?_)
      simpa only [e.left_inv hzs] using hU.mem_nhds hz.2
    obtain ⟨r, hr, hrN⟩ := Metric.mem_nhds_iff.mp hN
    have hfc : MDifferentiableOn 𝓘(ℂ, Model m) (model n) (f ∘ e.symm) (Metric.ball (e z) r) := by
      intro a ha
      exact ((hf.mdifferentiableAt (hU.mem_nhds (hrN ha).2)).comp a
        (mdifferentiableAt_atlas_symm (I := model m)
          (ChartedSpace.chart_mem_atlas z) (hrN ha).1)).mdifferentiableWithinAt
    have hgc : MDifferentiableOn 𝓘(ℂ, Model m) (model n) (g ∘ e.symm) (Metric.ball (e z) r) := by
      intro a ha
      exact ((hg.mdifferentiableAt (hU.mem_nhds (hrN ha).2)).comp a
        (mdifferentiableAt_atlas_symm (I := model m)
          (ChartedSpace.chart_mem_atlas z) (hrN ha).1)).mdifferentiableWithinAt
    have hB : e.source ∩ e ⁻¹' Metric.ball (e z) r ∈ 𝓝 z :=
      inter_mem (e.open_source.mem_nhds hzs) (hcz (Metric.ball_mem_nhds _ hr))
    obtain ⟨w, hwB, hwV⟩ := mem_closure_iff_nhds.mp hz.1 _ hB
    have hwgerm : (f ∘ e.symm) =ᶠ[𝓝 (e w)] (g ∘ e.symm) := by
      apply hwV.comp_tendsto
      have h := e.symm.continuousAt (e.map_source hwB.1)
      change Tendsto e.symm (𝓝 (e w)) (𝓝 (e.symm (e w))) at h
      simpa only [e.left_inv hwB.1] using h
    have heq := holomorphic_manifold_eqOn_of_preconnected_of_eventuallyEq
      Metric.isOpen_ball (convex_ball (e z) r).isPreconnected hfc hgc hwB.2 hwgerm
    exact Filter.mem_of_superset hB fun a ha ↦ by
      change f a = g a
      simpa only [Function.comp_apply, e.left_inv ha.1] using heq ha.2
  intro z hz
  exact (hVU hz).eq_of_nhds

end ManifoldSourceIdentity
end UniversalCoverSplitting

namespace UniversalCoverSplitting
section LocalProductSeparation
variable {E₁ E₂ F : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem independent_second_of_fderiv_zero
    {U : Set E₁} {V : Set E₂} (hU : IsOpen U) (hV : IsOpen V)
    (hVc : IsPreconnected V) {f : E₁ × E₂ → F}
    (hf : DifferentiableOn ℂ f (U ×ˢ V))
    (hzero : ∀ p ∈ U ×ˢ V, ∀ v : E₂, fderiv ℂ f p (0, v) = 0)
    {a : E₁} (ha : a ∈ U) {b c : E₂} (hb : b ∈ V) (hc : c ∈ V) :
    f (a, b) = f (a, c) := by
  have hd (y : E₂) (hy : y ∈ V) :
      HasFDerivAt (fun t : E₂ ↦ f (a, t)) (0 : E₂ →L[ℂ] F) y := by
    have hp : HasFDerivAt (fun t : E₂ ↦ (a, t))
        (ContinuousLinearMap.inr ℂ E₁ E₂) y := by
      have hh := (hasFDerivAt_const (𝕜 := ℂ) a y).prodMk (hasFDerivAt_id (𝕜 := ℂ) y)
      have he : (ContinuousLinearMap.prod (0 : E₂ →L[ℂ] E₁)
          (ContinuousLinearMap.id ℂ E₂)) = ContinuousLinearMap.inr ℂ E₁ E₂ := by
        ext v <;> rfl
      rw [he] at hh
      exact hh
    have hh := ((hf (a, y) ⟨ha, hy⟩).differentiableAt
      ((hU.prod hV).mem_nhds ⟨ha, hy⟩)).hasFDerivAt.comp y hp
    have he : fderiv ℂ f (a, y) ∘L ContinuousLinearMap.inr ℂ E₁ E₂ = 0 := by
      ext v
      exact hzero (a, y) ⟨ha, hy⟩ v
    rw [he] at hh
    exact hh
  exact hV.is_const_of_fderiv_eq_zero hVc
    (fun y hy ↦ (hd y hy).differentiableAt.differentiableWithinAt)
    (fun y hy ↦ (hd y hy).fderiv) hb hc

end LocalProductSeparation
end UniversalCoverSplitting

open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold ENNReal NNReal
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}
local instance [CompactSpace X.Carrier] : MetricSpace X.Carrier := compactManifoldMetric X

end UniversalCoverSplitting

end

end OAI
