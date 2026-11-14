/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.Analysis.Calculus.Deriv.Slope
import Tengoku.Seed.Analysis.Calculus.Deriv.Inv
import Tengoku.Seed.Analysis.Calculus.Deriv.Comp
import Tengoku.Seed.Analysis.Complex.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Complex differentiability and holomorphic functions

This file starts the textbook layer of complex analysis with the punctured-neighborhood
difference-quotient definition.  Mathlib's Fréchet derivative is used only through explicit bridge
theorems.  In particular, `HolomorphicOnTextbook f U` means that `f` is differentiable in a full
neighborhood of every point of `U`; it is equivalent to Mathlib's relative `DifferentiableOn ℂ`
only when `U` is open.

## Current entries

* `complex-analysis.holomorphic.definition`
* `complex-analysis.holomorphic.algebra`
-/

open Filter Set
open scoped Topology

namespace SandronesLibrary.ComplexAnalysis

/-- A complex function is complex differentiable at `z` when its punctured-neighborhood difference
quotient tends to a complex number.

> **Entry**: complex-analysis.holomorphic.definition-/
def ComplexDifferentiableAtTextbook (f : ℂ → ℂ) (z : ℂ) : Prop :=
  ∃ L : ℂ, Tendsto (fun w ↦ (f w - f z) / (w - z)) (nhdsWithin z {z}ᶜ) (nhds L)

/-- A function is holomorphic on `U` when it is complex differentiable, in a full neighborhood, at
every point of `U`.

This is deliberately stronger than relative differentiability on a nonopen set.  The full
neighborhood may depend on the point; no single neighborhood of all of `U` is asserted.

> **Entry**: complex-analysis.holomorphic.definition-/
def HolomorphicOnTextbook (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∀ z ∈ U, ComplexDifferentiableAtTextbook f z

/-- The punctured-neighborhood difference-quotient definition is equivalent to Mathlib's
complex-scalar differentiability at a point.-/
theorem complexDifferentiableAtTextbook_iff_differentiableAt {f : ℂ → ℂ} {z : ℂ} :
    ComplexDifferentiableAtTextbook f z ↔ DifferentiableAt ℂ f z := by
  constructor
  · rintro ⟨L, hL⟩
    have hfun : (fun w ↦ (f w - f z) / (w - z)) = slope f z :=
      funext fun w ↦ (slope_def_field f z w).symm
    rw [hfun] at hL
    exact (hasDerivAt_iff_tendsto_slope.mpr hL).differentiableAt
  · intro hf
    have hfun : (fun w ↦ (f w - f z) / (w - z)) = slope f z :=
      funext fun w ↦ (slope_def_field f z w).symm
    refine ⟨deriv f z, ?_⟩
    rw [hfun]
    exact hf.hasDerivAt.tendsto_slope

/-- Holomorphy on a set is pointwise Mathlib complex differentiability in full neighborhoods.-/
theorem holomorphicOnTextbook_iff_forall_differentiableAt {f : ℂ → ℂ} {U : Set ℂ} :
    HolomorphicOnTextbook f U ↔ ∀ z ∈ U, DifferentiableAt ℂ f z := by
  constructor
  · intro hf z hz
    exact complexDifferentiableAtTextbook_iff_differentiableAt.mp (hf z hz)
  · intro hf z hz
    exact complexDifferentiableAtTextbook_iff_differentiableAt.mpr (hf z hz)

/-- On an open set, the textbook full-neighborhood definition is equivalent to Mathlib's relative
`DifferentiableOn ℂ` predicate.  The openness hypothesis is essential for this reverse bridge.-/
theorem holomorphicOnTextbook_iff_differentiableOn {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) : HolomorphicOnTextbook f U ↔ DifferentiableOn ℂ f U := by
  rw [holomorphicOnTextbook_iff_forall_differentiableAt]
  constructor
  · intro hf z hz
    exact (hf z hz).differentiableWithinAt
  · intro hf z hz
    exact (hf z hz).differentiableAt (hU.mem_nhds hz)

/-- The sum of two functions holomorphic on `U` is holomorphic on `U`.

> **Entry**: complex-analysis.holomorphic.algebra-/
theorem holomorphicOnTextbook_add {f g : ℂ → ℂ} {U : Set ℂ}
    (hf : HolomorphicOnTextbook f U) (hg : HolomorphicOnTextbook g U) :
    HolomorphicOnTextbook (fun z ↦ f z + g z) U := by
  intro z hz
  apply complexDifferentiableAtTextbook_iff_differentiableAt.mpr
  exact (complexDifferentiableAtTextbook_iff_differentiableAt.mp (hf z hz)).add
    (complexDifferentiableAtTextbook_iff_differentiableAt.mp (hg z hz))

/-- The product of two functions holomorphic on `U` is holomorphic on `U`.-/
theorem holomorphicOnTextbook_mul {f g : ℂ → ℂ} {U : Set ℂ}
    (hf : HolomorphicOnTextbook f U) (hg : HolomorphicOnTextbook g U) :
    HolomorphicOnTextbook (fun z ↦ f z * g z) U := by
  intro z hz
  apply complexDifferentiableAtTextbook_iff_differentiableAt.mpr
  exact (complexDifferentiableAtTextbook_iff_differentiableAt.mp (hf z hz)).mul
    (complexDifferentiableAtTextbook_iff_differentiableAt.mp (hg z hz))

/-- A quotient of functions holomorphic on `U` is holomorphic wherever the denominator is
nonzero.-/
theorem holomorphicOnTextbook_div {f g : ℂ → ℂ} {U : Set ℂ}
    (hf : HolomorphicOnTextbook f U) (hg : HolomorphicOnTextbook g U)
    (hg0 : ∀ z ∈ U, g z ≠ 0) :
    HolomorphicOnTextbook (fun z ↦ f z / g z) U := by
  intro z hz
  apply complexDifferentiableAtTextbook_iff_differentiableAt.mpr
  exact (complexDifferentiableAtTextbook_iff_differentiableAt.mp (hf z hz)).div
    (complexDifferentiableAtTextbook_iff_differentiableAt.mp (hg z hz)) (hg0 z hz)

/-- If `g` maps `U` into `V`, composing a function holomorphic on `V` with one holomorphic on `U`
gives a function holomorphic on `U`.-/
theorem holomorphicOnTextbook_comp {f g : ℂ → ℂ} {U V : Set ℂ}
    (hf : HolomorphicOnTextbook f V) (hg : HolomorphicOnTextbook g U)
    (hmap : MapsTo g U V) :
    HolomorphicOnTextbook (f ∘ g) U := by
  intro z hz
  apply complexDifferentiableAtTextbook_iff_differentiableAt.mpr
  exact (complexDifferentiableAtTextbook_iff_differentiableAt.mp (hf (g z) (hmap hz))).comp z
    (complexDifferentiableAtTextbook_iff_differentiableAt.mp (hg z hz))

end SandronesLibrary.ComplexAnalysis
