/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.JacobianConstruction.Periods
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.LocalMultiplicity.ChartBridge
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Path.Perturb
public import Tengoku

/-!
# Generic points (Forster §21.3)

Unit: period-lattice-rank (`docs/design/period-lattice-rank.md` §6.2). There are `genus X`
distinct points `a₁,…,a_g ∈ X` such that any `ω ∈ Form1 X` vanishing at all `aⱼ` is identically
zero: Forster's proof is a strict descending induction on `dim ⋂ⱼ ker (evalAt aⱼ)`, using that a
nonzero holomorphic form is nonzero off any finite set (openness of the nonvanishing locus +
`RS.nonempty_open_diff_finite`).

Main declarations: `RS.isOpen_coeffAt_ne_zero`, `RS.exists_coeffAt_ne_zero_notMem`,
`RS.exists_genericPoints`, `RS.det_genericMatrix_ne_zero`.
-/

@[expose] public section

open scoped ContDiff Manifold
open Set Filter Topology IsManifold

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- `coeffAt x` bundled as a `ℂ`-linear functional. -/
def evalAtₗ (x : X) : Form1 X →ₗ[ℂ] ℂ where
  toFun η := coeffAt x η
  map_add' := coeffAt_add x
  map_smul' := coeffAt_smul x

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
@[simp] theorem evalAtₗ_apply (x : X) (η : Form1 X) : evalAtₗ x η = coeffAt x η := rfl

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- The nonvanishing locus of a form's coefficient is open. -/
theorem isOpen_coeffAt_ne_zero (η : Form1 X) : IsOpen {x : X | coeffAt x η ≠ 0} := by
  rw [isOpen_iff_mem_nhds]
  intro x₀ hx₀
  set e := chartAt ℂ x₀ with he_def
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X := chart_mem_maximalAtlas x₀
  have hne : coeffIn e η (e x₀) ≠ 0 := hx₀
  have hcont : ContinuousAt (coeffIn e η) (e x₀) :=
    (η.continuousOn_coeffIn he).continuousAt (e.open_target.mem_nhds (mem_chart_target ℂ x₀))
  have hev : ∀ᶠ z in 𝓝 (e x₀), coeffIn e η z ≠ 0 := hcont.eventually_ne hne
  have htend : Tendsto e (𝓝 x₀) (𝓝 (e x₀)) := e.continuousAt (mem_chart_source ℂ x₀)
  have h1 : e.source ∈ 𝓝 x₀ := e.open_source.mem_nhds (mem_chart_source ℂ x₀)
  filter_upwards [htend.eventually hev, h1] with x hx hxsrc
  show coeffAt x η ≠ 0
  have hz : chartAt ℂ x x ∈ ⇑(chartAt ℂ x) '' (e.source ∩ (chartAt ℂ x).source) :=
    ⟨x, ⟨hxsrc, mem_chart_source ℂ x⟩, rfl⟩
  have heq : coeffIn (chartAt ℂ x) η (chartAt ℂ x x) =
      deriv (⇑e ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) *
        coeffIn e η (e ((chartAt ℂ x).symm (chartAt ℂ x x))) :=
    coeffIn_trans he (chart_mem_maximalAtlas x) η hz
  rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)] at heq
  change (coeffIn (chartAt ℂ x) η (chartAt ℂ x x) : ℂ) ≠ 0
  rw [heq]
  exact mul_ne_zero
    (analyticAt_transition (chart_mem_maximalAtlas x) he (mem_chart_source ℂ x) hxsrc).2 hx

variable (X) in
/-- The submodule of forms vanishing at every point of `s`. -/
def genericKernel (s : Finset X) : Submodule ℂ (Form1 X) where
  carrier := {η | ∀ x ∈ s, coeffAt x η = 0}
  zero_mem' x _ := coeffAt_zero x
  add_mem' {η η'} hη hη' x hx := by rw [coeffAt_add, hη x hx, hη' x hx, add_zero]
  smul_mem' c η hη x hx := by rw [coeffAt_smul, hη x hx, mul_zero]

end RS

end
