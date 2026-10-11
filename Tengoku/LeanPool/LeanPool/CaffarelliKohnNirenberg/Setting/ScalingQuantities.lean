/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Statements.Theta
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Statements.Gamma
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Statements.Lambda

/-!
# Scale invariance of the dimensionless quantities

This module formalizes the rescaled fields of Definition `def:rescaling` of
`paper/ckn.tex` and the transformation law of Lemma `lem:scaling-quantities`:
at the rescaled base point each of `α`, `β`, `γ`, `δ`, `λ`, `θ` is unchanged
from its value at the original point with the radius scaled by the dilation.

The analytic input is the parabolic change of variables for cylinder integrals
and time-slice essential suprema, together with the elementary algebra of the
exponents.  The essential supremum of the velocity `L²` energy is handled with
the boundedness assumption that makes the transform of an essential supremum
legitimate; every other quantity is unconditional.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Pointwise
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration

noncomputable section

namespace CKN

/-! ### The rescaled fields -/

/-- The velocity component of the parabolically rescaled solution of Definition
`def:rescaling`: `u^{μ,z₀}(y,s) = μ u(x₀ + μ y, t₀ + μ² s)`. -/
noncomputable def rescaleVelocity (μ : ℝ) (z₀ : ParabolicPoint)
    (u : ParabolicPoint → Vec3) : ParabolicPoint → Vec3 :=
  fun w => μ • u (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ w))

/-- The pressure component of the parabolically rescaled solution of Definition
`def:rescaling`: `p^{μ,z₀}(y,s) = μ² p(x₀ + μ y, t₀ + μ² s)`. -/
noncomputable def rescalePressure (μ : ℝ) (z₀ : ParabolicPoint)
    (p : ParabolicPoint → ℝ) : ParabolicPoint → ℝ :=
  fun w => μ ^ 2 * p (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ w))

/-- The force component of the parabolically rescaled solution of Definition
`def:rescaling`: `f^{μ,z₀}(y,s) = μ³ f(x₀ + μ y, t₀ + μ² s)`. -/
noncomputable def rescaleForce (μ : ℝ) (z₀ : ParabolicPoint)
    (f : ParabolicPoint → Vec3) : ParabolicPoint → Vec3 :=
  fun w => μ ^ 3 • f (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ w))

/-- The rescaled spatial gradient datum matching `rescaleVelocity`: the chain
rule gives `∇(u^{μ,z₀}) = μ² (∇u) ∘ T` for `T(y,s) = (x₀ + μ y, t₀ + μ² s)`. -/
noncomputable def rescaleGradient (μ : ℝ) (z₀ : ParabolicPoint)
    (Du : ParabolicPoint → Fin 3 → Vec3) : ParabolicPoint → Fin 3 → Vec3 :=
  fun w i => μ ^ 2 • Du (parabolicTranslate z₀.1 z₀.2 (parabolicScale μ w)) i

/-! ### The underlying affine map and its Jacobian -/

/-- The spatial part `y ↦ x + a y` of the parabolic rescaling. -/
def spatialAffine (a : ℝ) (x : Vec3) : Vec3 → Vec3 := fun y => x + a • y

/-- The time part `s ↦ t + a² s` of the parabolic rescaling. -/
def timeAffine (a : ℝ) (t : ℝ) : ℝ → ℝ := fun s => t + a ^ 2 * s

/-- The parabolic rescaling map `z ↦ (x₀ + μ z₁, t₀ + μ² z₂)`. -/
def parabolicAffine (a : ℝ) (x : Vec3) (t : ℝ) : ParabolicPoint → ParabolicPoint :=
  fun z => parabolicTranslate x t (parabolicScale a z)

/-! ### Exponential algebra -/

/-! ### The Dirichlet energy `β` -/

/-! ### The velocity `L²` energy `α` -/

/-! ### The velocity cubic quantity `γ` -/

/-! ### The pressure quantity `δ` -/

/-! ### The force quantity `λ` -/

/-! ### The iteration quantity `θ` -/

end CKN

end
