/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import Tengoku.FormalMathfin.MathFin.BlackScholes.AmericanPut.Stopping.CompactKernelDerivative

/-! # Heat equation for the continuous compact-data boundary integral 
## Result

Public entry points include `heatPartial`, `heatPartial_smoothAt`, `heatPartial_time`, `heatPartial_space`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory
open scoped Topology ContDiff

/-- The derivative of `F` at the plane point `z` along the direction `v`, read off the Fréchet
derivative `fderiv ℝ F z`. -/
noncomputable def heatPartial (F : ℝ × ℝ → ℝ) (v z : ℝ × ℝ) : ℝ :=
  fderiv ℝ F z v

/--
@isnad1 id=contdiff.1h3v.s7.6a89144f5fd3 from=translated src=- shape=35158f43 vocab=919a8acf
-/
theorem heatPartial_smoothAt {F : ℝ × ℝ → ℝ} {z : ℝ × ℝ}
    (hF : ContDiffAt ℝ ∞ F z) (v : ℝ × ℝ) :
    ContDiffAt ℝ ∞ (heatPartial F v) z :=
  (hF.fderiv_right (by simp)).clm_apply contDiffAt_const

/--
@isnad1 id=hasderiv.1h3v.s7.50905b98e848 from=translated src=- shape=87034154 vocab=b63e83ca
-/
theorem heatPartial_time {F : ℝ × ℝ → ℝ} {t x : ℝ}
    (hF : DifferentiableAt ℝ F (t,x)) :
    HasDerivAt (fun s => F (s,x)) (heatPartial F (1,0) (t,x)) t := by
  convert! hF.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x)) using 1

/--
@isnad1 id=hasderiv.1h3v.s7.d7e39becf7da from=translated src=- shape=285cc3ad vocab=b63e83ca
-/
theorem heatPartial_space {F : ℝ × ℝ → ℝ} {t x : ℝ}
    (hF : DifferentiableAt ℝ F (t,x)) :
    HasDerivAt (fun y => F (t,y)) (heatPartial F (0,1) (t,x)) x := by
  convert! hF.hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_const x t).prodMk (hasDerivAt_id x)) using 1

/-- The causal heat boundary kernel as one function of the plane point `z = (t,x)`. -/
noncomputable def boundaryKernelPlane (z : ℝ × ℝ) : ℝ := causalHeatBoundaryKernel z.1 z.2

/--
@isnad1 id=contdiff.1h1v.s6.1f24bd191cfe from=translated src=- shape=215530c5 vocab=7a1a88ed
-/
theorem boundaryKernelPlane_smoothAt {z : ℝ × ℝ} (hx : 0 < z.2) :
    ContDiffAt ℝ ∞ boundaryKernelPlane z := causalHeatBoundaryKernel_smoothAt hx.ne'

/--
@isnad1 id=eq.1h2v.s6.9de3edf8e908 from=translated src=- shape=1ed33e2d vocab=c8c2abcd
-/
theorem boundaryKernelPlane_equation (t : ℝ) {x : ℝ} (hx : 0 < x) :
    heatPartial boundaryKernelPlane (1,0) (t,x) =
      (1/2)*heatPartial (heatPartial boundaryKernelPlane (0,1)) (0,1) (t,x) := by
  have ht := heatPartial_time (t := t) ((boundaryKernelPlane_smoothAt hx).differentiableAt (by simp))
  have hd := heatPartial_space
    ((heatPartial_smoothAt (boundaryKernelPlane_smoothAt (z := (t,x)) hx) (0,1)).differentiableAt (by simp))
  have he : (fun y => heatPartial boundaryKernelPlane (0,1) (t,y)) =ᶠ[𝓝 x]
      deriv (causalHeatBoundaryKernel t) := by
    filter_upwards [lt_mem_nhds hx] with y hy
    exact (heatPartial_space ((boundaryKernelPlane_smoothAt hy).differentiableAt (by simp))).deriv.symm
  rw [← ht.deriv,← hd.deriv,he.deriv_eq]
  exact causalHeatBoundaryKernel_equation t hx

/--
@isnad1 id=hasderiv.3h3v.s7.798e9c1f835a from=translated src=- shape=adfcadd5 vocab=20438e09
-/
theorem compact_causalBoundaryIntegral_hasDeriv_time {g : ℝ → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) {x : ℝ} (hx : 0 < x) (t : ℝ) :
    HasDerivAt (fun s => causalBoundaryIntegral g x s)
      (∫ y, heatPartial boundaryKernelPlane (1,0) (t-y,x)*g y) t := by
  apply compact_kernelIntegral_hasDeriv hg hc (U := univ)
    (F := fun s y => boundaryKernelPlane (s-y,x))
    (F' := fun s y => heatPartial boundaryKernelPlane (1,0) (s-y,x)) isOpen_univ
  · intro z _
    exact ((boundaryKernelPlane_smoothAt hx).continuousAt.comp
      (show ContinuousAt (fun z : ℝ × ℝ => (z.1-z.2,x)) z by fun_prop)).continuousWithinAt
  · intro z _
    exact ((heatPartial_smoothAt (boundaryKernelPlane_smoothAt hx) (1,0)).continuousAt.comp
      (show ContinuousAt (fun z : ℝ × ℝ => (z.1-z.2,x)) z by fun_prop)).continuousWithinAt
  · intro s _ y
    convert! (heatPartial_time
      ((boundaryKernelPlane_smoothAt hx).differentiableAt (by simp))).comp s
      ((hasDerivAt_id s).sub_const y) using 1
    simp
  · exact mem_univ _

/--
@isnad1 id=hasderiv.4h4v.s8.d783c1885e78 from=translated src=- shape=71b6b26c vocab=f58f6108
-/
theorem compact_planeIntegral_hasDeriv_space {g : ℝ → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) {F : ℝ × ℝ → ℝ}
    (hF : ∀ z, 0 < z.2 → ContDiffAt ℝ ∞ F z) {x : ℝ} (hx : 0 < x) (t : ℝ) :
    HasDerivAt (fun x => ∫ y, F (t-y,x)*g y)
      (∫ y, heatPartial F (0,1) (t-y,x)*g y) x := by
  apply compact_kernelIntegral_hasDeriv hg hc (U := Ioi 0)
    (F := fun s y => F (t-y,s))
    (F' := fun s y => heatPartial F (0,1) (t-y,s)) isOpen_Ioi
  · intro z hz
    exact ((hF (t-z.2,z.1) hz.1).continuousAt.comp (f := fun w : ℝ × ℝ => (t-w.2,w.1))
      (show ContinuousAt (fun z : ℝ × ℝ => (t-z.2,z.1)) z by fun_prop)).continuousWithinAt
  · intro z hz
    exact ((heatPartial_smoothAt (hF (t-z.2,z.1) hz.1) (0,1)).continuousAt.comp
      (f := fun w : ℝ × ℝ => (t-w.2,w.1))
      (show ContinuousAt (fun z : ℝ × ℝ => (t-z.2,z.1)) z by fun_prop)).continuousWithinAt
  · intro s hs y
    exact heatPartial_space ((hF (t-y,s) hs).differentiableAt (by simp))
  · exact hx

/--
@isnad1 id=eq.3h3v.s7.adb39628f223 from=translated src=- shape=de2586b8 vocab=42d33727
-/
theorem compact_causalBoundaryIntegral_equation {g : ℝ → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) {x : ℝ} (hx : 0 < x) (t : ℝ) :
    deriv (fun s => causalBoundaryIntegral g x s) t =
      (1/2)*deriv (deriv (fun x => causalBoundaryIntegral g x t)) x := by
  have hF : ∀ z, 0 < z.2 → ContDiffAt ℝ ∞ boundaryKernelPlane z :=
    fun _ hz => boundaryKernelPlane_smoothAt hz
  have hD : ∀ z, 0 < z.2 → ContDiffAt ℝ ∞ (heatPartial boundaryKernelPlane (0,1)) z :=
    fun z hz => heatPartial_smoothAt (hF z hz) (0,1)
  have he : deriv (fun x => causalBoundaryIntegral g x t) =ᶠ[𝓝 x]
      (fun x => ∫ y, heatPartial boundaryKernelPlane (0,1) (t-y,x)*g y) := by
    filter_upwards [lt_mem_nhds hx] with u hu
    exact (compact_planeIntegral_hasDeriv_space hg hc hF hu t).deriv
  rw [(compact_causalBoundaryIntegral_hasDeriv_time hg hc hx t).deriv,he.deriv_eq,
    (compact_planeIntegral_hasDeriv_space hg hc hD hx t).deriv,← integral_const_mul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  dsimp only
  rw [boundaryKernelPlane_equation (t-y) hx]
  ring

/--
@isnad1 id=eq.3h3v.s7.cb923c0671f6 from=translated src=- shape=de2586b8 vocab=ef52bb88
-/
theorem compact_heatBoundaryExtension_equation {g : ℝ → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) {x : ℝ} (hx : 0 < x) (t : ℝ) :
    deriv (fun s => heatBoundaryExtension g x s) t =
      (1/2)*deriv (deriv (fun x => heatBoundaryExtension g x t)) x := by
  have ht : (fun s => heatBoundaryExtension g x s) = fun s => causalBoundaryIntegral g x s :=
    funext fun s => heatBoundaryExtension_eq_causalBoundaryIntegral g hx s
  have hx' : (fun u => heatBoundaryExtension g u t) =ᶠ[𝓝 x]
      (fun u => causalBoundaryIntegral g u t) := by
    filter_upwards [lt_mem_nhds hx] with u hu
    exact heatBoundaryExtension_eq_causalBoundaryIntegral g hu t
  rw [ht,hx'.deriv.deriv_eq]
  exact compact_causalBoundaryIntegral_equation hg hc hx t

/-- Constructed half-line solution for continuous compact boundary data that starts at `a`.
This is not a solution matching both ends of a finite interval.
@isnad1 id=ex.3h2v.s8.f8ae6c16e2e5 from=translated src=- shape=b48cfb28 vocab=701adbe2
-/
theorem exists_halfLine_heat_boundary_solution {g : ℝ → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) {a : ℝ}
    (hstart : ∀ t, t ≤ a → g t = 0) :
    ∃ V : ℝ × ℝ → ℝ, Continuous V ∧
      (∀ t, V (0,t) = g t) ∧
      (∀ x t, t ≤ a → V (x,t) = 0) ∧
      ContDiffOn ℝ ∞ V {z | 0 < z.1} ∧
      ∀ x, 0 < x → ∀ t, deriv (fun s => V (x,s)) t =
        (1/2)*deriv (deriv (fun y => V (y,t))) x := by
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous hg
  exact ⟨fun z => heatBoundaryExtension g z.1 z.2,
    heatBoundaryExtension_continuous hg hC,heatBoundaryExtension_boundary g,
    fun x _ ht => heatBoundaryExtension_causal hstart x ht,
    compact_heatBoundaryExtension_smooth hg hc,
    fun _ hx t => compact_heatBoundaryExtension_equation hg hc hx t⟩

end MathFin.BlackScholes.AmericanPut.Stopping
