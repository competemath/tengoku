/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Forms.Coeffs
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Surface.Bridges

/-!
# Analyticity characterization of holomorphic 1-forms (CC1, design §2.2)

Unit: holomorphic-forms (`docs/design/holomorphic-forms.md`). This file proves the CC1
statement "`coeffIn` is analytic iff the section is `ω`-smooth", using the canonical
`ContMDiffAt ↔ AnalyticAt` bridge from the surfaces-and-charts unit (`Jacobian.Surface.Bridges`)
instead of a local re-proof.

Main declarations:
* `RS.analyticAt_trans` — transitions between maximal-atlas charts are analytic.
* `RS.deriv_trans_comp` — chain rule for transition derivatives through a third chart.
* `RS.tangentCoord_mfderiv_comp` — scalar chain rule: the `mfderiv`-composite read in the
  canonical tangent coordinate is the planar `deriv` of the composite.
* `RS.contMDiffAt_section_iff_analyticAt_coeffInFun` — a covector section is `C^ω` at `x` iff
  its coefficient function in the preferred chart is analytic at `chartAt ℂ x x`.
* `RS.Form1.ofSectionAnalytic` — constructor for `Form1` from a raw section with analytic
  preferred-chart coefficients.
* `RS.Form1.analyticAt_coeffAt`, `RS.Form1.analyticOnNhd_coeffIn`,
  `RS.Form1.continuousOn_coeffIn` — coefficients of holomorphic 1-forms are analytic on chart
  targets (any maximal-atlas chart).
-/

@[expose] public section

open scoped ContDiff Manifold Bundle
open Set IsManifold
open ContinuousLinearMap (inCoordinates)

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Analyticity and derivatives of transition maps -/

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- The transition map between two maximal-atlas charts is analytic at every point of the image
of the overlap.
@isnad1 id=analytic.4h4v.s8.c9048a3ce05d from=translated src=- shape=5a615e1a vocab=1ebd4170
-/
theorem analyticAt_trans {e e' : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) (he' : e' ∈ maximalAtlas 𝓘(ℂ) ω X) {z : ℂ}
    (hzt : z ∈ e'.target) (hzs : e'.symm z ∈ e.source) :
    AnalyticAt ℂ (⇑e ∘ ⇑e'.symm) z := by
  have hcompat := StructureGroupoid.compatible_of_mem_maximalAtlas he' he
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hcompat
  have h1 : ContDiffOn ℂ ω (⇑𝓘(ℂ) ∘ ⇑(e'.symm.trans e) ∘ ⇑𝓘(ℂ).symm)
      (⇑𝓘(ℂ).symm ⁻¹' (e'.symm.trans e).source ∩ Set.range ⇑𝓘(ℂ)) := hcompat.1
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id,
    Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ] at h1
  have hzsrc : z ∈ (e'.symm.trans e).source := by
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
    exact ⟨hzt, hzs⟩
  have hCD : ContDiffAt ℂ ω ⇑(e'.symm.trans e) z :=
    h1.contDiffAt ((e'.symm.trans e).open_source.mem_nhds hzsrc)
  have hcoe : ⇑(e'.symm.trans e) = ⇑e ∘ ⇑e'.symm := rfl
  have hA : AnalyticAt ℂ ⇑(e'.symm.trans e) z := hCD.analyticAt
  rwa [hcoe] at hA

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Chain rule for transition derivatives: reading the transition from `f` to `e` through an
intermediate chart `e'` multiplies the derivatives.
@isnad1 id=eq.6h5v.s9.1a7826985ca0 from=translated src=- shape=dae22575 vocab=456b42a6
-/
theorem deriv_trans_comp {e e' f : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) (he' : e' ∈ maximalAtlas 𝓘(ℂ) ω X)
    (hf : f ∈ maximalAtlas 𝓘(ℂ) ω X) {z : ℂ} (hzt : z ∈ f.target)
    (hes : f.symm z ∈ e.source) (he's : f.symm z ∈ e'.source) :
    deriv (⇑e ∘ ⇑f.symm) z =
      deriv (⇑e ∘ ⇑e'.symm) (e' (f.symm z)) * deriv (⇑e' ∘ ⇑f.symm) z := by
  have hWopen : IsOpen (⇑f '' (e.source ∩ e'.source ∩ f.source)) :=
    f.isOpen_image_of_subset_source
      ((e.open_source.inter e'.open_source).inter f.open_source) inter_subset_right
  have hzW : z ∈ ⇑f '' (e.source ∩ e'.source ∩ f.source) :=
    ⟨f.symm z, ⟨⟨hes, he's⟩, f.map_target hzt⟩, f.right_inv hzt⟩
  have heq : ⇑e ∘ ⇑f.symm =ᶠ[nhds z] (⇑e ∘ ⇑e'.symm) ∘ (⇑e' ∘ ⇑f.symm) := by
    filter_upwards [hWopen.mem_nhds hzW] with w hw
    obtain ⟨q, hq, rfl⟩ := hw
    simp only [Function.comp_apply, f.left_inv hq.2, e'.left_inv hq.1.2]
  have h1 : DifferentiableAt ℂ (⇑e ∘ ⇑e'.symm) (e' (f.symm z)) :=
    differentiableAt_trans he he' (e'.map_source he's)
      (by rw [e'.left_inv he's]; exact hes)
  have h2 : DifferentiableAt ℂ (⇑e' ∘ ⇑f.symm) z := differentiableAt_trans he' hf hzt he's
  rw [heq.deriv_eq]
  exact deriv_comp z h1 h2

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- **Scalar chain rule**: the composite of `mfderiv`s applied to the canonical tangent vector
`1`, read in the canonical coordinate, is the planar derivative of the composite.
@isnad1 id=eq.2h4v.s11.1d13c1db5e57 from=translated src=- shape=19d98bcb vocab=e520d5cf
-/
theorem tangentCoord_mfderiv_comp {f : X → ℂ} {g : ℂ → X} {z : ℂ}
    (hf : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f (g z)) (hg : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g z) :
    tangentCoord (mfderiv 𝓘(ℂ) 𝓘(ℂ) f (g z) (mfderiv 𝓘(ℂ) 𝓘(ℂ) g z (1 : ℂ))) =
      deriv (f ∘ g) z := by
  have hmf : mfderiv 𝓘(ℂ) 𝓘(ℂ) (f ∘ g) z =
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) f (g z)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) g z) := mfderiv_comp z hf hg
  calc tangentCoord (mfderiv 𝓘(ℂ) 𝓘(ℂ) f (g z) (mfderiv 𝓘(ℂ) 𝓘(ℂ) g z (1 : ℂ)))
      = tangentCoord (mfderiv 𝓘(ℂ) 𝓘(ℂ) (f ∘ g) z (1 : ℂ)) := by rw [hmf]; rfl
    _ = deriv (f ∘ g) z := by rw [mfderiv_eq_fderiv]; rfl

/-! ### The planar `(ℂ →L[ℂ] ℂ)`-valued analyticity reduction -/

/-- A `ℂ →L[ℂ] ℂ`-valued map is analytic iff its pointwise evaluation at `1` is (the fiber is
one-dimensional; evaluation at `1` is a linear isometry equivalence).
@isnad1 id=iff.0h2v.s8.2cc263a30ee7 from=translated src=- shape=33a3395a vocab=e62dd8a6
-/
theorem analyticAt_clm_iff_apply_one {F : ℂ → ℂ →L[ℂ] ℂ} {z : ℂ} :
    AnalyticAt ℂ F z ↔ AnalyticAt ℂ (fun w => F w 1) z := by
  set L := (ContinuousLinearMap.toSpanSingletonLIE ℂ ℂ).symm with hL
  constructor
  · intro h
    have h1 : AnalyticAt ℂ (fun w => L.toContinuousLinearEquiv (F w)) z :=
      AnalyticAt.fun_comp (g := ⇑L.toContinuousLinearEquiv) (f := F)
        ((L.toContinuousLinearEquiv : (ℂ →L[ℂ] ℂ) →L[ℂ] ℂ).analyticAt (F z)) h
    exact h1.congr (Filter.Eventually.of_forall fun w => rfl)
  · intro h
    have h1 : AnalyticAt ℂ (fun w => L.toContinuousLinearEquiv.symm (F w 1)) z :=
      AnalyticAt.fun_comp (g := ⇑L.toContinuousLinearEquiv.symm) (f := fun w => F w 1)
        ((L.toContinuousLinearEquiv.symm : ℂ →L[ℂ] (ℂ →L[ℂ] ℂ)).analyticAt (F z 1)) h
    refine h1.congr (Filter.Eventually.of_forall fun w => ?_)
    change L.toContinuousLinearEquiv.symm (L.toContinuousLinearEquiv (F w)) = F w
    exact L.toContinuousLinearEquiv.symm_apply_apply (F w)

/-- Defeq bridge: the hom-bundle trivialization representative of a covector section, evaluated
at the canonical tangent vector `1`, is the chart coefficient function.
@isnad1 id=eq.1h4v.s10.aa6260598e2e from=translated src=- shape=4528cd1c vocab=a6b0382e
-/
theorem inCoordinates_apply_one (σ : ∀ x : X, TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial X ℂ x)
    (x : X) {z : ℂ} (hz : z ∈ (chartAt ℂ x).target) :
    inCoordinates ℂ (TangentSpace 𝓘(ℂ)) ℂ (Bundle.Trivial X ℂ) x ((chartAt ℂ x).symm z) x
        ((chartAt ℂ x).symm z) (σ ((chartAt ℂ x).symm z)) (1 : ℂ) =
      coeffInFun (chartAt ℂ x) σ z := by
  have hp : (chartAt ℂ x).symm z ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hz
  -- the domain (tangent) factor is the mfderiv of the chart inverse
  have hdom : (trivializationAt ℂ (TangentSpace 𝓘(ℂ)) x).symmL ℂ ((chartAt ℂ x).symm z) (1 : ℂ) =
      mfderiv 𝓘(ℂ) 𝓘(ℂ) (⇑(chartAt ℂ x).symm) z (1 : ℂ) := by
    rw [TangentBundle.symmL_trivializationAt hp]
    simp only [extChartAt_coe_symm, extChartAt_coe, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.comp_id, Set.range_id,
      mfderivWithin_univ, Function.comp_apply, id_eq]
    rw [(chartAt ℂ x).right_inv hz]
    rfl
  -- the codomain (trivial-bundle) factor is the identity
  have hcod : ∀ w : ℂ,
      (Bundle.Trivial.trivialization X ℂ).continuousLinearMapAt ℂ
        ((chartAt ℂ x).symm z) w = w := by
    intro w
    rw [Bundle.Trivial.continuousLinearMapAt_trivialization]
    rfl
  calc inCoordinates ℂ (TangentSpace 𝓘(ℂ)) ℂ (Bundle.Trivial X ℂ) x ((chartAt ℂ x).symm z) x
        ((chartAt ℂ x).symm z) (σ ((chartAt ℂ x).symm z)) (1 : ℂ)
      = (trivializationAt ℂ (Bundle.Trivial X ℂ) x).continuousLinearMapAt ℂ
          ((chartAt ℂ x).symm z)
          (evalC σ ((chartAt ℂ x).symm z)
            ((trivializationAt ℂ (TangentSpace 𝓘(ℂ)) x).symmL ℂ ((chartAt ℂ x).symm z)
              (1 : ℂ))) := rfl
    _ = evalC σ ((chartAt ℂ x).symm z)
          ((trivializationAt ℂ (TangentSpace 𝓘(ℂ)) x).symmL ℂ ((chartAt ℂ x).symm z)
            (1 : ℂ)) := hcod _
    _ = evalC σ ((chartAt ℂ x).symm z)
          (mfderiv 𝓘(ℂ) 𝓘(ℂ) (⇑(chartAt ℂ x).symm) z (1 : ℂ)) := by rw [hdom]
    _ = coeffInFun (chartAt ℂ x) σ z := rfl

/-! ### The section characterization -/

/-- **Smoothness ↔ analytic coefficients** (CC1): a covector section is `C^ω` at `x` iff its
coefficient function in the preferred chart at `x` is analytic at the chart image of `x`.
@isnad1 id=iff.0h3v.s12.c5ca99f06131 from=translated src=- shape=650044d5 vocab=02ff74d1
-/
theorem contMDiffAt_section_iff_analyticAt_coeffInFun
    (σ : ∀ x : X, TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial X ℂ x) (x : X) :
    ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
        (fun p => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) p (σ p)) x ↔
      AnalyticAt ℂ (coeffInFun (chartAt ℂ x) σ) (chartAt ℂ x x) := by
  rw [Bundle.contMDiffAt_section, contMDiffAt_iff_analyticAt_comp_chartAt,
    analyticAt_clm_iff_apply_one]
  refine analyticAt_congr ?_
  filter_upwards [(chartAt ℂ x).open_target.mem_nhds (mem_chart_target ℂ x)] with z hz
  exact inCoordinates_apply_one σ x hz

/-- Build a holomorphic 1-form from a raw covector section whose preferred-chart coefficient
functions are analytic. -/
def Form1.ofSectionAnalytic (σ : ∀ x : X, TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial X ℂ x)
    (h : ∀ x, AnalyticAt ℂ (coeffInFun (chartAt ℂ x) σ) (chartAt ℂ x x)) : Form1 X :=
  ⟨σ, fun x => (contMDiffAt_section_iff_analyticAt_coeffInFun σ x).mpr (h x)⟩

/--
@isnad1 id=eq.1h2v.s11.909a2ec7f4ea from=translated src=- shape=e12f64c2 vocab=fbc918c9
-/
@[simp]
theorem Form1.coe_ofSectionAnalytic (σ : ∀ x : X, TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial X ℂ x)
    (h : ∀ x, AnalyticAt ℂ (coeffInFun (chartAt ℂ x) σ) (chartAt ℂ x x)) :
    ⇑(Form1.ofSectionAnalytic σ h) = σ := rfl

/-! ### Analyticity of the coefficients of a holomorphic 1-form -/

/-- The coefficient of a holomorphic 1-form in the preferred chart at `x` is analytic at the
chart image of `x`.
@isnad1 id=analytic.0h3v.s7.d39c6b896ba7 from=translated src=- shape=1938b0aa vocab=6469fbd3
-/
theorem Form1.analyticAt_coeffAt (η : Form1 X) (x : X) :
    AnalyticAt ℂ (coeffIn (chartAt ℂ x) η) (chartAt ℂ x x) :=
  (contMDiffAt_section_iff_analyticAt_coeffInFun (⇑η) x).mp (η.contMDiff x)

/-- The coefficient of a holomorphic 1-form in any maximal-atlas chart is analytic on the whole
chart target.
@isnad1 id=analytic.1h3v.s8.cf7fd3ed3952 from=translated src=- shape=fd860a02 vocab=2bb6dde1
-/
theorem Form1.analyticOnNhd_coeffIn (η : Form1 X) {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) : AnalyticOnNhd ℂ (coeffIn e η) e.target := by
  intro z hz
  have hps : e.symm z ∈ e.source := e.map_target hz
  have hchart : chartAt ℂ (e.symm z) ∈ maximalAtlas 𝓘(ℂ) ω X := chart_mem_maximalAtlas _
  -- the open overlap image around `z`
  have hWopen : IsOpen (⇑e '' ((chartAt ℂ (e.symm z)).source ∩ e.source)) :=
    e.isOpen_image_of_subset_source
      ((chartAt ℂ (e.symm z)).open_source.inter e.open_source) inter_subset_right
  have hzW : z ∈ ⇑e '' ((chartAt ℂ (e.symm z)).source ∩ e.source) :=
    ⟨e.symm z, ⟨mem_chart_source ℂ (e.symm z), hps⟩, e.right_inv hz⟩
  -- transition rule to the preferred chart at the base point
  have heq : coeffIn e η =ᶠ[nhds z]
      fun w => deriv (⇑(chartAt ℂ (e.symm z)) ∘ ⇑e.symm) w *
        coeffIn (chartAt ℂ (e.symm z)) η ((⇑(chartAt ℂ (e.symm z)) ∘ ⇑e.symm) w) := by
    filter_upwards [hWopen.mem_nhds hzW] with w hw
    exact coeffIn_trans hchart he η hw
  -- the transported function is analytic at `z`
  have hτ : AnalyticAt ℂ (⇑(chartAt ℂ (e.symm z)) ∘ ⇑e.symm) z :=
    analyticAt_trans hchart he hz (mem_chart_source ℂ (e.symm z))
  have hτz : (⇑(chartAt ℂ (e.symm z)) ∘ ⇑e.symm) z = chartAt ℂ (e.symm z) (e.symm z) := rfl
  have hcoeff : AnalyticAt ℂ
      (fun w => coeffIn (chartAt ℂ (e.symm z)) η ((⇑(chartAt ℂ (e.symm z)) ∘ ⇑e.symm) w)) z := by
    refine AnalyticAt.fun_comp ?_ hτ
    rw [hτz]
    exact η.analyticAt_coeffAt (e.symm z)
  exact (AnalyticAt.fun_mul hτ.deriv hcoeff).congr heq.symm

/-- The coefficient of a holomorphic 1-form in a maximal-atlas chart is analytic at each target
point (pointwise form).
@isnad1 id=analytic.2h4v.s8.df8340b6cced from=translated src=- shape=d8bc6855 vocab=36044ada
-/
theorem Form1.analyticAt_coeffIn (η : Form1 X) {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) {z : ℂ} (hz : z ∈ e.target) :
    AnalyticAt ℂ (coeffIn e η) z :=
  η.analyticOnNhd_coeffIn he z hz

/-- Coefficients of holomorphic 1-forms are continuous on chart targets.
@isnad1 id=continuo.1h3v.s8.0b5bf2aa6088 from=translated src=- shape=fdaab68d vocab=ac872050
-/
theorem Form1.continuousOn_coeffIn (η : Form1 X) {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) : ContinuousOn (coeffIn e η) e.target :=
  (η.analyticOnNhd_coeffIn he).continuousOn

end RS

end
