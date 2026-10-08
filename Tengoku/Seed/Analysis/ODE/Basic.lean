/-
Copyright (c) 2025 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Calculus.Deriv.Basic

/-!
# Integral curves of vector fields on a normed vector space

Let `E` be a normed vector space and `v : ℝ → E → E` be a time-dependent vector field on `E`.
An integral curve  of `v` is a function `γ : ℝ → E` such that the derivative of `γ` at `t` equals
`v t (γ t)`. The integral curve may only be defined for all `t` within some subset of `ℝ`.

## Main definitions

Let `v : ℝ → E → E` be a time-dependent vector field on `E`, and let `γ : ℝ → E`.
* `IsIntegralCurve γ v`: `γ t` is tangent to `v t (γ t)` for all `t : ℝ`. That is, `γ` is a global
  integral curve of `v`.
* `IsIntegralCurveOn γ v s`: `γ t` is tangent to `v t (γ t)` for all `t ∈ s`, where `s : Set ℝ`.
* `IsIntegralCurveAt γ v t₀`: `γ t` is tangent to `v t (γ t)` for all `t` in some open interval
  around `t₀`. That is, `γ` is a local integral curve of `v`.

## TODO

* Implement `IsIntegralCurveWithinAt`.

## Tags

integral curve, vector field
-/

@[expose] public section

open scoped Topology

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `IsIntegralCurveOn γ v s` means `γ t` is tangent to `v t (γ t)` within `s` for all `t ∈ s`. -/
def IsIntegralCurveOn (γ : ℝ → E) (v : ℝ → E → E) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasDerivWithinAt γ (v t (γ t)) s t

/-- `IsIntegralCurveAt γ v t₀` means `γ : ℝ → E` is a local integral curve of `v` in a neighbourhood
containing `t₀`. -/
def IsIntegralCurveAt (γ : ℝ → E) (v : ℝ → E → E) (t₀ : ℝ) : Prop :=
  ∀ᶠ t in 𝓝 t₀, HasDerivAt γ (v t (γ t)) t

/-- `IsIntegralCurve γ v` means `γ : ℝ → E` is a global integral curve of `v`. That is, `γ t` is
tangent to `v t (γ t)` for all `t : ℝ`. -/
def IsIntegralCurve (γ : ℝ → E) (v : ℝ → E → E) : Prop :=
  ∀ t : ℝ, HasDerivAt γ (v t (γ t)) t

variable {γ : ℝ → E} {v : ℝ → E → E} {s s' : Set ℝ} {t₀ : ℝ}

/--
@isnad1 id=isintegr.1h4v.s5.47d78d949fcf from=seed src=0 shape=f678932c vocab=1f4c5436
-/
lemma IsIntegralCurve.isIntegralCurveOn (h : IsIntegralCurve γ v) (s : Set ℝ) :
    IsIntegralCurveOn γ v s := fun t _ ↦ (h t).hasDerivWithinAt

/--
@isnad1 id=iff.0h3v.s5.f432fd5e7123 from=seed src=0 shape=2b5eb5f7 vocab=d6c36da2
-/
lemma isIntegralCurveOn_univ :
    IsIntegralCurveOn γ v univ ↔ IsIntegralCurve γ v :=
  ⟨fun h t ↦ (h t (mem_univ _)).hasDerivAt Filter.univ_mem, fun h ↦ h.isIntegralCurveOn _⟩

/--
@isnad1 id=iff.0h4v.s5.d52f7d614c84 from=seed src=0 shape=9af2c95b vocab=c2dc7c95
-/
lemma isIntegralCurveAt_iff_exists_mem_nhds :
    IsIntegralCurveAt γ v t₀ ↔ ∃ s ∈ 𝓝 t₀, IsIntegralCurveOn γ v s := by
  rw [IsIntegralCurveAt, Filter.eventually_iff_exists_mem]
  refine ⟨fun ⟨s, hs, h⟩ ↦ ⟨s, hs, fun t ht ↦ (h t ht).hasDerivWithinAt⟩, ?_⟩
  intro ⟨s, hs, h⟩
  rw [mem_nhds_iff] at hs
  obtain ⟨s', h₁, h₂, h₃⟩ := hs
  refine ⟨s', h₂.mem_nhds h₃, ?_⟩
  intro t ht
  apply (h t (h₁ ht)).hasDerivAt
  rw [mem_nhds_iff]
  exact ⟨s', h₁, h₂, ht⟩

/-- `γ` is an integral curve for `v` at `t₀` iff `γ` is an integral curve on some interval
containing `t₀`.
@isnad1 id=iff.0h4v.s5.6aed179baf98 from=seed src=0 shape=ac3bcdb6 vocab=b1f16385
-/
lemma isIntegralCurveAt_iff_exists_pos :
    IsIntegralCurveAt γ v t₀ ↔ ∃ ε > 0, IsIntegralCurveOn γ v (Metric.ball t₀ ε) := by
  rw [IsIntegralCurveAt, Metric.eventually_nhds_iff_ball]
  congrm ∃ ε > 0, ∀ (y : ℝ) (hy : y ∈ Metric.ball t₀ ε), ?_
  exact ⟨HasDerivAt.hasDerivWithinAt, fun h ↦ h.hasDerivAt (Metric.isOpen_ball.mem_nhds hy)⟩

/--
@isnad1 id=isintegr.1h4v.s5.1ac692865782 from=seed src=0 shape=a213d5aa vocab=d1b7c4d4
-/
lemma IsIntegralCurve.isIntegralCurveAt (h : IsIntegralCurve γ v) (t : ℝ) :
    IsIntegralCurveAt γ v t :=
  isIntegralCurveAt_iff_exists_mem_nhds.mpr
    ⟨univ, Filter.univ_mem, fun t _ ↦ (h t).hasDerivWithinAt⟩

/--
@isnad1 id=iff.0h3v.s5.64b4e9d0d789 from=seed src=0 shape=0b73a6f0 vocab=d1b7c4d4
-/
lemma isIntegralCurve_iff_isIntegralCurveAt :
    IsIntegralCurve γ v ↔ ∀ t : ℝ, IsIntegralCurveAt γ v t :=
  ⟨fun h ↦ h.isIntegralCurveAt, fun h t ↦ by
    obtain ⟨s, hs, h⟩ := isIntegralCurveAt_iff_exists_mem_nhds.mp (h t)
    exact h t (mem_of_mem_nhds hs) |>.hasDerivAt hs⟩

/--
@isnad1 id=isintegr.2h5v.s5.7ccbf9820b0f from=seed src=0 shape=b1eb84dc vocab=46a963ff
-/
lemma IsIntegralCurveOn.mono (h : IsIntegralCurveOn γ v s) (hs : s' ⊆ s) :
    IsIntegralCurveOn γ v s' := fun t ht ↦ h t (hs ht) |>.mono hs

/--
@isnad1 id=hasderiv.1h4v.s6.1ce14700fd0b from=seed src=0 shape=157f7d7f vocab=acce48b8
-/
lemma IsIntegralCurveAt.hasDerivAt (h : IsIntegralCurveAt γ v t₀) :
    HasDerivAt γ (v t₀ (γ t₀)) t₀ :=
  have ⟨_, hs, h⟩ := isIntegralCurveAt_iff_exists_mem_nhds.mp h
  h t₀ (mem_of_mem_nhds hs) |>.hasDerivAt hs

/--
@isnad1 id=isintegr.2h5v.s5.ed0017fe971a from=seed src=0 shape=a7fb54aa vocab=c2dc7c95
-/
lemma IsIntegralCurveOn.isIntegralCurveAt (h : IsIntegralCurveOn γ v s) (hs : s ∈ 𝓝 t₀) :
    IsIntegralCurveAt γ v t₀ := isIntegralCurveAt_iff_exists_mem_nhds.mpr ⟨s, hs, h⟩

/-- If `γ` is an integral curve at each `t ∈ s`, it is an integral curve on `s`.
@isnad1 id=isintegr.1h4v.s5.fd2b934f9205 from=seed src=0 shape=83de3ea4 vocab=e0b4227f
-/
lemma IsIntegralCurveAt.isIntegralCurveOn (h : ∀ t ∈ s, IsIntegralCurveAt γ v t) :
    IsIntegralCurveOn γ v s := by
  intros t ht
  obtain ⟨s', hs', h⟩ := Filter.eventually_iff_exists_mem.mp (h t ht)
  exact h _ (mem_of_mem_nhds hs') |>.hasDerivWithinAt

/--
@isnad1 id=iff.1h4v.s5.ecbc9f968349 from=seed src=0 shape=b293bfbe vocab=dfece6ca
-/
lemma isIntegralCurveOn_iff_isIntegralCurveAt (hs : IsOpen s) :
    IsIntegralCurveOn γ v s ↔ ∀ t ∈ s, IsIntegralCurveAt γ v t :=
  ⟨fun h _ ht ↦ h.isIntegralCurveAt (hs.mem_nhds ht), IsIntegralCurveAt.isIntegralCurveOn⟩

/--
@isnad1 id=continuo.2h5v.s6.bcd3a8eaca0f from=seed src=0 shape=557b4e16 vocab=7dc7e690
-/
lemma IsIntegralCurveOn.continuousWithinAt (hγ : IsIntegralCurveOn γ v s) (ht : t₀ ∈ s) :
    ContinuousWithinAt γ s t₀ := (hγ t₀ ht).continuousWithinAt

/--
@isnad1 id=continuo.1h4v.s5.c474625a56fd from=seed src=0 shape=e978ec60 vocab=e4a055e3
-/
lemma IsIntegralCurveOn.continuousOn (hγ : IsIntegralCurveOn γ v s) :
    ContinuousOn γ s := (hγ · · |>.continuousWithinAt)

/--
@isnad1 id=continuo.1h4v.s5.b6d261eddef3 from=seed src=0 shape=190634e0 vocab=7030de3d
-/
lemma IsIntegralCurveAt.continuousAt (hγ : IsIntegralCurveAt γ v t₀) :
    ContinuousAt γ t₀ :=
  have ⟨_, hs, hγ⟩ := isIntegralCurveAt_iff_exists_mem_nhds.mp hγ
  hγ.continuousWithinAt (mem_of_mem_nhds hs) |>.continuousAt hs

/--
@isnad1 id=continuo.1h3v.s5.f12abc57e3db from=seed src=0 shape=7b8e603f vocab=ceac7021
-/
lemma IsIntegralCurve.continuous (hγ : IsIntegralCurve γ v) : Continuous γ :=
  continuous_iff_continuousAt.mpr (hγ.isIntegralCurveAt · |>.continuousAt)
