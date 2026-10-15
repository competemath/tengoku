/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Dbar.Form01
public import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Dbar.Wirtinger
public import Tengoku
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Dbar.SolveDisk
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Forms.Analyticity
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Surface.Bridges
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Surface.RealSmooth

/-!
# The intrinsic `dbar` operator and `IsDbarOn` (`Jacobian/Dbar/Operator.lean`)

Unit: dbar-solvability (`docs/design/dbar-solvability.md` D6/D7, §4.7, §7.3-4).

`SmoothC X` is a hand-rolled subtype `{f : X → ℂ // ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ f}` with our OWN
`AddCommGroup`/`Module ℂ` instances (per design D6: mathlib's bundled `ContMDiffMap` ring/module
instances only give a `Module ℝ` for our target model `𝓘(ℝ,ℂ)`, and layering a competing `ℂ`
scalar action on mathlib's own type is exactly the `restrictScalars` diamond trap the blueprint
warns about — a private subtype dodges it). Closure under the ring/module operations, and the
chart-representative smoothness needed for `dbar`, are proved via the CC7 bridge
`contMDiffAt_real_iff_contDiffAt` (`Jacobian.Surface.RealSmooth`) and the composition
`ContMDiffOn.comp` with `contMDiffOn_extChartAt_symm` (mathlib), reduced to `ContDiffOn ℝ` via
`contMDiffOn_iff_contDiffOn` — this avoids needing any project-local "chart invariance for real
smoothness" lemma (`extChartAt 𝓘(ℂ) x` coincides with `chartAt ℂ x` definitionally, `Compat`
bridge facts checked in-line).

The intrinsic `dbar : SmoothC X →ₗ[ℂ] Form01 X` is chart-local `wirtingerDbar` of the chart
representative; `IsDbarAt`/`IsDbarOn` are the chart-free (evaluated-at-centers) local dbar-equation
predicates (D7); `exists_dbar_solution_chart_ball` transports Forster 13.2 (`SolveDisk.lean`)
through a chart.
-/

@[expose] public section

open scoped ContDiff Manifold
open Set IsManifold

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### `SmoothC X`: real-smooth `ℂ`-valued functions, with `ℂ`-linear structure -/

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Real-smooth `ℂ`-valued functions on `X`, as a private subtype (D6). -/
def SmoothC (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] :
    Type _ :=
  {f : X → ℂ // ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f}

namespace SmoothC

instance : FunLike (SmoothC X) X ℂ where
  coe f := f.1
  coe_injective _ _ h := Subtype.ext h

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/--
@isnad1 id=contmdif.0h2v.s7.bd2132418d1a from=translated src=- shape=07fc2c20 vocab=9b035c01
-/
theorem contMDiff (f : SmoothC X) : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (⇑f) := f.2

/-- **Compat** (design §4.7): the chart representative of a `SmoothC` function is planar-smooth
on the whole chart target (not just at the chart's own centre): compose the globally `ContMDiff`
function with the (mathlib) chart-inverse smoothness `contMDiffOn_extChartAt_symm`, then reduce
`ContMDiff` on planar sets to `ContDiff` via `contMDiffOn_iff_contDiffOn`.
@isnad1 id=contdiff.0h3v.s7.152e7d61d567 from=translated src=- shape=1bff1ddf vocab=834a8edf
-/
theorem contDiffOn_comp_chartAt_symm (f : SmoothC X) (x : X) :
    ContDiffOn ℝ ∞ (⇑f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x).target := by
  have hg : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (⇑f) Set.univ := f.contMDiff.contMDiffOn
  have hf' : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (⇑(chartAt ℂ x).symm) (chartAt ℂ x).target := by
    have h1 := contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, ℂ)) (n := (∞ : ℕ∞ω)) x
    have htarget : (extChartAt 𝓘(ℝ, ℂ) x).target = (chartAt ℂ x).target := by simp
    rwa [htarget] at h1
  have hcomp : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (⇑f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x).target :=
    hg.comp hf' (fun z _ => Set.mem_univ _)
  exact contMDiffOn_iff_contDiffOn.1 hcomp

/--
@isnad1 id=contdiff.0h3v.s7.4d04b20583d6 from=translated src=- shape=9853b825 vocab=530c8ab9
-/
theorem contDiffAt_comp_chartAt_symm_self (f : SmoothC X) (x : X) :
    ContDiffAt ℝ ∞ (⇑f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
  (f.contDiffOn_comp_chartAt_symm x).contDiffAt
    ((chartAt ℂ x).open_target.mem_nhds (mem_chart_target ℂ x))

/--
@isnad1 id=differen.1h4v.s8.0aab8e82d9a6 from=translated src=- shape=ad9646f7 vocab=fea62630
-/
theorem differentiableAt_comp_chartAt_symm (f : SmoothC X) (x : X) {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target) :
    DifferentiableAt ℝ (⇑f ∘ ⇑(chartAt ℂ x).symm) z :=
  ((f.contDiffOn_comp_chartAt_symm x).contDiffAt
    ((chartAt ℂ x).open_target.mem_nhds hz)).differentiableAt (by norm_num)

/-- Chart-local closure helper: if the chart representatives of `f` are `ContDiffAt` at every
chart centre, `f` is `ContMDiff`. -/
private theorem contMDiff_of_chart_op {f : X → ℂ}
    (h : ∀ x, ContDiffAt ℝ ∞ (f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x)) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f := fun x => contMDiffAt_real_iff_contDiffAt.2 (h x)

instance : Add (SmoothC X) where
  add f g := ⟨fun x => f x + g x, private_decl% (contMDiff_of_chart_op fun x =>
    (f.contDiffAt_comp_chartAt_symm_self x).add (g.contDiffAt_comp_chartAt_symm_self x))⟩

instance : Neg (SmoothC X) where
  neg f := ⟨fun x => -f x, private_decl% (contMDiff_of_chart_op fun x =>
    (f.contDiffAt_comp_chartAt_symm_self x).neg)⟩

instance : Sub (SmoothC X) where
  sub f g := ⟨fun x => f x - g x, private_decl% (contMDiff_of_chart_op fun x =>
    (f.contDiffAt_comp_chartAt_symm_self x).sub (g.contDiffAt_comp_chartAt_symm_self x))⟩

instance : Zero (SmoothC X) where
  zero := ⟨fun _ => 0, private_decl% (contMDiff_of_chart_op fun _ => contDiffAt_const)⟩

instance : SMul ℂ (SmoothC X) where
  smul c f := ⟨fun x => c * f x, private_decl% (contMDiff_of_chart_op fun x =>
    (ContinuousLinearMap.mul ℝ ℂ c).contDiff.contDiffAt.comp _
      (f.contDiffAt_comp_chartAt_symm_self x))⟩

/--
@isnad1 id=eq.0h4v.s7.21a1438867dd from=translated src=- shape=2949b89d vocab=fded70fe
-/
@[simp] theorem coe_add (f g : SmoothC X) (x : X) : (f + g) x = f x + g x := rfl
/--
@isnad1 id=eq.0h3v.s6.b3df9dd42c64 from=translated src=- shape=c05bbead vocab=5fc3aac6
-/
@[simp] theorem coe_neg (f : SmoothC X) (x : X) : (-f) x = -f x := rfl
/--
@isnad1 id=eq.0h4v.s7.112a5d988891 from=translated src=- shape=2949b89d vocab=df2ab8d3
-/
@[simp] theorem coe_sub (f g : SmoothC X) (x : X) : (f - g) x = f x - g x := rfl
/--
@isnad1 id=eq.0h2v.s6.3f93d969c26a from=translated src=- shape=fd54cc20 vocab=de3caf55
-/
@[simp] theorem coe_zero (x : X) : (0 : SmoothC X) x = 0 := rfl
/--
@isnad1 id=eq.0h4v.s7.d48df8e1811e from=translated src=- shape=1b62a455 vocab=d2d4e47d
-/
@[simp] theorem coe_smul (c : ℂ) (f : SmoothC X) (x : X) : (c • f) x = c * f x := rfl

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/--
@isnad1 id=eq.1h3v.s6.9d0fff9e8688 from=translated src=- shape=198b49fc vocab=86c4f4bc
-/
theorem ext' {f g : SmoothC X} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.coe_injective (funext h)

instance : AddCommGroup (SmoothC X) where
  add_assoc a b c := ext' fun x => by simp [add_assoc]
  zero_add a := ext' fun x => by simp
  add_zero a := ext' fun x => by simp
  add_comm a b := ext' fun x => by simp [add_comm]
  neg_add_cancel a := ext' fun x => by simp
  sub_eq_add_neg a b := ext' fun x => by simp [sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module ℂ (SmoothC X) where
  smul_zero a := ext' fun x => by simp
  smul_add a b c := ext' fun x => by simp [mul_add]
  add_smul a b c := ext' fun x => by simp [add_mul]
  zero_smul a := ext' fun x => by simp
  one_smul a := ext' fun x => by simp
  mul_smul a b c := ext' fun x => by simp [mul_assoc]

end SmoothC

/-! ### The intrinsic `dbar` -/

/-- The raw coefficient family underlying `dbar f`: chart-local `wirtingerDbar` of the chart
representative of `f`, junk-zero off the chart target. -/
def dbarCoeffAt (f : SmoothC X) (x : X) : ℂ → ℂ :=
  (chartAt ℂ x).target.indicator (fun z => wirtingerDbar (⇑f ∘ ⇑(chartAt ℂ x).symm) z)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
private theorem dbarCoeffAt_of_mem (f : SmoothC X) (x : X) {z : ℂ} (hz : z ∈ (chartAt ℂ x).target) :
    dbarCoeffAt f x z = wirtingerDbar (⇑f ∘ ⇑(chartAt ℂ x).symm) z :=
  Set.indicator_of_mem hz _

private theorem dbarCoeffAt_compat (f : SmoothC X) (x y : X) (z : ℂ)
    (hz : z ∈ ⇑(chartAt ℂ y) '' ((chartAt ℂ x).source ∩ (chartAt ℂ y).source)) :
    dbarCoeffAt f y z = (starRingEnd ℂ) (deriv (⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ y).symm) z) *
      dbarCoeffAt f x (chartAt ℂ x ((chartAt ℂ y).symm z)) := by
  obtain ⟨p, ⟨hpx, hpy⟩, rfl⟩ := hz
  have hty : chartAt ℂ y p ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hpy
  have htx : chartAt ℂ x p ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hpx
  rw [(chartAt ℂ y).left_inv hpy, dbarCoeffAt_of_mem f y hty, dbarCoeffAt_of_mem f x htx]
  set τ : ℂ → ℂ := ⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ y).symm with hτ_def
  have hzs : (chartAt ℂ y).symm (chartAt ℂ y p) ∈ (chartAt ℂ x).source := by
    rw [(chartAt ℂ y).left_inv hpy]; exact hpx
  have hτ_an : AnalyticAt ℂ τ (chartAt ℂ y p) :=
    analyticAt_trans (chart_mem_maximalAtlas x) (chart_mem_maximalAtlas y) hty hzs
  have hτ_diff : DifferentiableAt ℂ τ (chartAt ℂ y p) := hτ_an.differentiableAt
  have hτ_pt : τ (chartAt ℂ y p) = chartAt ℂ x p := by
    simp only [hτ_def, Function.comp_apply, (chartAt ℂ y).left_inv hpy]
  have hFx_diff : DifferentiableAt ℝ (⇑f ∘ ⇑(chartAt ℂ x).symm) (τ (chartAt ℂ y p)) := by
    rw [hτ_pt]; exact f.differentiableAt_comp_chartAt_symm x htx
  have hWopen : IsOpen (⇑(chartAt ℂ y) '' ((chartAt ℂ x).source ∩ (chartAt ℂ y).source)) :=
    (chartAt ℂ y).isOpen_image_of_subset_source
      ((chartAt ℂ x).open_source.inter (chartAt ℂ y).open_source) inter_subset_right
  have hzW : chartAt ℂ y p ∈ ⇑(chartAt ℂ y) '' ((chartAt ℂ x).source ∩ (chartAt ℂ y).source) :=
    ⟨p, ⟨hpx, hpy⟩, rfl⟩
  have heq : (⇑f ∘ ⇑(chartAt ℂ y).symm) =ᶠ[nhds (chartAt ℂ y p)]
      (⇑f ∘ ⇑(chartAt ℂ x).symm) ∘ τ := by
    filter_upwards [hWopen.mem_nhds hzW] with w hw
    obtain ⟨q, ⟨hqx, hqy⟩, rfl⟩ := hw
    simp only [Function.comp_apply, hτ_def, (chartAt ℂ y).left_inv hqy,
      (chartAt ℂ x).left_inv hqx]
  rw [wirtingerDbar_congr_nhds _ _ (chartAt ℂ y p) heq,
    wirtingerDbar_comp_differentiableAt (⇑f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ y p) hFx_diff hτ_diff,
    hτ_pt]

/-- The intrinsic `dbar`, chart-locally the planar Wirtinger operator. -/
noncomputable def dbar : SmoothC X →ₗ[ℂ] Form01 X where
  toFun f :=
    { coeffAt := dbarCoeffAt f
      coeffAt_zero_off := fun x z hz => Set.indicator_of_notMem hz _
      contDiffOn_coeffAt := fun x => by
        apply (contDiffOn_wirtingerDbar (⇑f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x).open_target
          (f.contDiffOn_comp_chartAt_symm x)).congr
        intro z hz
        exact dbarCoeffAt_of_mem f x hz
      compat := private dbarCoeffAt_compat f }
  map_add' f g := by
    apply Form01.ext
    intro x z hz
    change dbarCoeffAt (f + g) x z = dbarCoeffAt f x z + dbarCoeffAt g x z
    rw [dbarCoeffAt_of_mem (f + g) x hz, dbarCoeffAt_of_mem f x hz, dbarCoeffAt_of_mem g x hz]
    have heq : (⇑(f + g) : X → ℂ) ∘ ⇑(chartAt ℂ x).symm =
        (⇑f ∘ ⇑(chartAt ℂ x).symm) + (⇑g ∘ ⇑(chartAt ℂ x).symm) := by
      funext w; simp
    rw [heq]
    have hp := (chartAt ℂ x).map_target hz
    exact wirtingerDbar_add _ _ z (f.differentiableAt_comp_chartAt_symm x hz)
      (g.differentiableAt_comp_chartAt_symm x hz)
  map_smul' c f := by
    apply Form01.ext
    intro x z hz
    change dbarCoeffAt (c • f) x z = c * dbarCoeffAt f x z
    rw [dbarCoeffAt_of_mem (c • f) x hz, dbarCoeffAt_of_mem f x hz]
    have heq : (⇑(c • f) : X → ℂ) ∘ ⇑(chartAt ℂ x).symm =
        fun w => c * (⇑f ∘ ⇑(chartAt ℂ x).symm) w := by
      funext w; simp
    rw [heq, wirtingerDbar_const_mul _ z c (f.differentiableAt_comp_chartAt_symm x hz)]

/--
@isnad1 id=eq.1h4v.s8.9fc7d9b31412 from=translated src=- shape=6a460a68 vocab=65ba270b
-/
@[simp]
theorem coeffAt_dbar (f : SmoothC X) (x : X) {z : ℂ} (hz : z ∈ (chartAt ℂ x).target) :
    (dbar f).coeffAt x z = wirtingerDbar (⇑f ∘ ⇑(chartAt ℂ x).symm) z :=
  dbarCoeffAt_of_mem f x hz

/-! ### `IsDbarAt` / `IsDbarOn` (D7): chart-free local `dbar`-equations -/

/-- `u` solves `dbaru = η` at `x`, evaluated in `x`'s own preferred chart. -/
def IsDbarAt (u : X → ℂ) (η : Form01 X) (x : X) : Prop :=
  wirtingerDbar (u ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) = η.coeffAt x (chartAt ℂ x x)

/-- `u` solves `dbaru = η` at every point of `s`. -/
def IsDbarOn (u : X → ℂ) (η : Form01 X) (s : Set X) : Prop := ∀ x ∈ s, IsDbarAt u η x

/-! ### Chart-disk solvability -/

end RS
