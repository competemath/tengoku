/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Analysis.PDE.SymmetricEnergy
public import Tengoku.Tauceti.TauCeti.MeasureTheory.Function.Lp.BilinearForm

/-!
# Variable-coefficient energy forms on `L²` jets

A divergence-form operator with bounded coefficients has an associated bounded bilinear form, its
energy form.  `TauCeti.Analysis.PDE.EnergyForm.Lp` treats constant coefficients; this file supplies
the variable-coefficient construction.  An essentially bounded field of pointwise continuous
bilinear forms acts by Hölder multiplication

`L∞(X; J →L J →L ℝ) × L²(X; J) → L²(X; J →L ℝ)`,

and the result pairs with a second `L²` jet.  Both operations are Mathlib's
`ContinuousLinearMap.holderL` and `ContinuousLinearMap.lpPairing`.

For PDE coefficients `a`, `b`, and `c`, the pointwise form is
`energyIntegrand (a x) (b x) (c x)`.  Requiring this field to belong to `L∞` is the precise
boundedness and measurability hypothesis needed by the construction.  The resulting form is
bundled and continuous, so later Sobolev value-gradient jets can feed it without carrying
integrability proofs at each use site.

## Main declarations

* `TauCeti.PDE.energyFormLpVariable`: the variable-coefficient divergence-form energy form.
* `TauCeti.PDE.energyFormLpVariable_apply`: its characterization by the expected energy
  integral.

No formal source is vendored.  The construction directly composes Mathlib's Hölder map and
`Lᵖ` pairing from `Mathlib.MeasureTheory.Function.Holder`.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open ENNReal MeasureTheory

variable {X : Type*} [MeasurableSpace X]

section Energy

open Matrix

variable {n : Type*} [Fintype n]

/-- The variable-coefficient divergence-form energy form on square-integrable value-gradient
jets.

The `MemLp ... ⊤ μ` argument records exactly that the pointwise energy forms are strongly
measurable and essentially bounded.  Its proof is irrelevant to the resulting form. -/
noncomputable def energyFormLpVariable (μ : Measure X) (a : X → Matrix n n ℝ)
    (b : X → EuclideanSpace ℝ n) (c : X → ℝ)
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ μ) :
    Lp (ℝ × EuclideanSpace ℝ n) 2 μ →L[ℝ]
      Lp (ℝ × EuclideanSpace ℝ n) 2 μ →L[ℝ] ℝ :=
  lpBilinearForm μ (hcoeff.toLp (fun x ↦ energyIntegrand (a x) (b x) (c x)))

/-- The variable-coefficient `L²` energy form is the integral of the pointwise jet energy
density. -/
@[simp]
theorem energyFormLpVariable_apply (μ : Measure X) (a : X → Matrix n n ℝ)
    (b : X → EuclideanSpace ℝ n) (c : X → ℝ)
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ μ)
    (U V : Lp (ℝ × EuclideanSpace ℝ n) 2 μ) :
    energyFormLpVariable μ a b c hcoeff U V =
      ∫ x, energyIntegrand (a x) (b x) (c x) (U x) (V x) ∂μ := by
  rw [energyFormLpVariable, lpBilinearForm_apply]
  apply integral_congr_ae
  have hcoe :
      (hcoeff.toLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) :
        X → ℝ × EuclideanSpace ℝ n →L[ℝ] ℝ × EuclideanSpace ℝ n →L[ℝ] ℝ) =ᵐ[μ]
          fun x ↦ energyIntegrand (a x) (b x) (c x) := hcoeff.coeFn_toLp
  filter_upwards [hcoe] with x hx
  rw [hx]

end Energy

end PDE

end TauCeti

end
