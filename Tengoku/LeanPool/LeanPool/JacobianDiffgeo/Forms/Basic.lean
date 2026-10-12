/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Tengoku

/-!
# Holomorphic 1-forms: the definition (CC1)

This file defines `RS.Form1 X`, the space of global holomorphic 1-forms on a Riemann surface
`X`, as bundled `C^ω` sections of the bundle of `ℂ`-linear maps from the (holomorphic) tangent
bundle to the trivial line bundle. This is the frozen core choice CC1 of
`docs/design/core-choices.md`; the spelling is verified by the compiled spike
`scratch_forms.lean`.

The `AddCommGroup`/`Module ℂ` structure and the `ω`-smooth vector bundle instance for the Hom
bundle are all found by typeclass inference (checked by the `example`s below). Evaluation
`η x v : ℂ` works through the reducible `Bundle.Trivial X ℂ x ≡ ℂ`.
-/

@[expose] public section

open scoped ContDiff Manifold Bundle

noncomputable section

namespace RS

variable (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The space of global holomorphic 1-forms on `X`: bundled `C^ω` sections of the bundle of
`ℂ`-linear maps from the (holomorphic) tangent bundle to the trivial line bundle.

Downstream units interact with `Form1` exclusively through the chart-coefficient API
`RS.coeffIn` (see `Jacobian/Forms/Coeffs.lean`), never through bundle internals. -/
abbrev Form1 : Type _ :=
  Cₛ^ω⟮𝓘(ℂ); ℂ →L[ℂ] ℂ, fun x : X => TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial X ℂ x⟯

variable {X}

-- Sanity checks (spike-verified): the algebraic instances are found by TC inference.

/-- Extensionality for holomorphic 1-forms from pointwise (covector-level) agreement. -/
theorem Form1.ext' {η η' : Form1 X} (h : ∀ x, η x = η' x) : η = η' :=
  ContMDiffSection.ext h

/-- Extensionality for holomorphic 1-forms from pointwise agreement on tangent vectors. -/
theorem Form1.ext_apply {η η' : Form1 X} (h : ∀ x, ∀ v : TangentSpace 𝓘(ℂ) x, η x v = η' x v) :
    η = η' :=
  Form1.ext' fun x => ContinuousLinearMap.ext fun v => h x v

end RS

end
