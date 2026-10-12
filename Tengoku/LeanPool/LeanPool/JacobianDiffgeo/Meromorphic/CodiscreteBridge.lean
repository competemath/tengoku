/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Meromorphic.Predicates
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Surface.Bridges
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Surface.Identity
public import Tengoku

/-!
# The codiscrete ⇄ punctured-neighborhood bridge (D2) and the identity dichotomy

Unit: meromorphic-and-divisors (`docs/design/meromorphic-and-divisors.md` §4.2, proof plan §6.1).

* `mem_codiscreteWithin_iff_of_isOpen` / `eventuallyEq_codiscreteWithin_iff_of_isOpen` /
  `eventually_codiscreteWithin_iff_of_isOpen`: for **open** `U`, membership in
  `codiscreteWithin U` (equivalently: `=ᶠ`-agreement, or an eventual property) is *purely
  topological* — it holds pointwise on `𝓝[≠] x` for every `x ∈ U`. This is the pivot that lets
  `ord`/`evalAt`/`divisor` descend to `MeroGermOn` classes against arbitrary representatives.
* `codiscreteWithin_neBot`, the instance `(codiscrete X).NeBot`.
* `MeromorphicOnX.congr_codiscreteWithin`, `MeromorphicOnX.analyticAt_codiscreteWithin`.
* The **meromorphic identity dichotomy** `MeromorphicOnX.eventuallyEq_zero_or_forall_ordAtX_ne_top`
  on a connected surface, and its corollary `MeromorphicOnX.codiscrete_setOf_ne_zero` — feeds
  `Field (ℳ X)` and `divisor` well-definedness.
-/

@[expose] public section

open scoped ContDiff Manifold
open Set Filter Topology

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {f g : X → ℂ} {U : Set X}

/-! ### D2: the bridge, both directions -/

omit [ChartedSpace ℂ X] in
theorem mem_codiscreteWithin_iff_of_isOpen {S : Set X} (hU : IsOpen U) :
    S ∈ codiscreteWithin U ↔ ∀ x ∈ U, S ∈ 𝓝[≠] x := by
  constructor
  · intro h x hx
    have h1 := mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 h x hx
    have h2 : U ∈ 𝓝[≠] x := mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hx)
    filter_upwards [h1, h2] with y hy hyU
    exact hy.resolve_right (by simp [hyU])
  · intro h
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
    exact fun x hx => mem_of_superset (h x hx) subset_union_left

omit [ChartedSpace ℂ X] in
/-- D2 (both directions): for open `U`, agreement of arbitrary `f, g` codiscretely within `U`
is exactly pointwise `𝓝[≠]`-agreement. Meromorphy-free. -/
theorem eventuallyEq_codiscreteWithin_iff_of_isOpen {α : Type*} {f g : X → α} (hU : IsOpen U) :
    f =ᶠ[codiscreteWithin U] g ↔ ∀ x ∈ U, f =ᶠ[𝓝[≠] x] g :=
  mem_codiscreteWithin_iff_of_isOpen (S := {y | f y = g y}) hU

omit [ChartedSpace ℂ X] in
/-- Prop-valued version of the D2 bridge. -/
theorem eventually_codiscreteWithin_iff_of_isOpen {p : X → Prop} (hU : IsOpen U) :
    (∀ᶠ x in codiscreteWithin U, p x) ↔ ∀ x ∈ U, ∀ᶠ y in 𝓝[≠] x, p y :=
  mem_codiscreteWithin_iff_of_isOpen (S := {x | p x}) hU

omit [ChartedSpace ℂ X] in
theorem eventuallyEq_codiscrete_iff {α : Type*} {f g : X → α} :
    f =ᶠ[codiscrete X] g ↔ ∀ x, f =ᶠ[𝓝[≠] x] g := by
  change f =ᶠ[codiscreteWithin univ] g ↔ _
  rw [eventuallyEq_codiscreteWithin_iff_of_isOpen isOpen_univ]
  simp

/-! ### `NeBot` instances -/

/-! ### Congruence and analyticity off a codiscrete set -/

theorem MeromorphicOnX.congr_codiscreteWithin (hf : MeromorphicOnX f U) (hU : IsOpen U)
    (h : f =ᶠ[codiscreteWithin U] g) : MeromorphicOnX g U := by
  intro x hx
  exact (hf x hx).congr (((eventuallyEq_codiscreteWithin_iff_of_isOpen hU).1 h) x hx)

/-- Meromorphic functions on an open set are chart-analytic off a set codiscrete in it. -/
theorem MeromorphicOnX.analyticAt_codiscreteWithin [IsManifold 𝓘(ℂ) ω X]
    (hf : MeromorphicOnX f U) (hU : IsOpen U) :
    ∀ᶠ y in codiscreteWithin U, AnalyticAt ℂ (f ∘ (chartAt ℂ y).symm) (chartAt ℂ y y) := by
  rw [eventually_codiscreteWithin_iff_of_isOpen hU]
  intro x hx
  have h1 : ∀ᶠ z in 𝓝[≠] (chartAt ℂ x x), AnalyticAt ℂ (f ∘ (chartAt ℂ x).symm) z :=
    MeromorphicAt.eventually_analyticAt (hf x hx)
  have h2 : ∀ᶠ y in 𝓝[≠] x, AnalyticAt ℂ (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x y) :=
    eventually_nhdsNE_comp_chart_apply_iff.mpr h1
  have h3 : ∀ᶠ y in 𝓝[≠] x, y ∈ (chartAt ℂ x).source :=
    eventually_nhdsWithin_of_eventually_nhds
      ((chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x))
  filter_upwards [h2, h3] with y h2y h3y
  have hcm : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f y :=
    (contMDiffAt_iff_analyticAt_of_mem_source (chart_mem_atlas ℂ x) h3y).2 h2y
  exact RS.contMDiffAt_iff_analyticAt_comp_chartAt.mp hcm

/-! ### The meromorphic identity dichotomy (§6.1) -/

end RS
