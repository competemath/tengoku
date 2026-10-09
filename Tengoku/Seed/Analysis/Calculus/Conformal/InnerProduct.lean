/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Calculus.Conformal.NormedSpace
public import Tengoku.Seed.Analysis.InnerProductSpace.ConformalLinearMap

/-!
# Conformal maps between inner product spaces

A function between inner product spaces which has a derivative at `x`
is conformal at `x` iff the derivative preserves inner products up to a scalar multiple.
-/

@[expose] public section


noncomputable section

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]

open RealInnerProductSpace

/-- A real differentiable map `f` is conformal at point `x` if and only if its
differential `fderiv ℝ f x` at that point scales every inner product by a positive scalar.
@isnad1 id=iff.0h4v.s9.e3fecfbc44b2 from=seed src=0 shape=79108e84 vocab=42d85c50
-/
theorem conformalAt_iff' {f : E → F} {x : E} : ConformalAt f x ↔
    ∃ c : ℝ, 0 < c ∧ ∀ u v : E, ⟪fderiv ℝ f x u, fderiv ℝ f x v⟫ = c * ⟪u, v⟫ := by
  rw [conformalAt_iff_isConformalMap_fderiv, isConformalMap_iff]

/-- A real differentiable map `f` is conformal at point `x` if and only if its
differential `f'` at that point scales every inner product by a positive scalar.
@isnad1 id=iff.1h5v.s9.50456c680360 from=seed src=0 shape=0fd2060c vocab=9830d43b
-/
theorem conformalAt_iff {f : E → F} {x : E} {f' : E →L[ℝ] F} (h : HasFDerivAt f f' x) :
    ConformalAt f x ↔ ∃ c : ℝ, 0 < c ∧ ∀ u v : E, ⟪f' u, f' v⟫ = c * ⟪u, v⟫ := by
  simp only [conformalAt_iff', h.fderiv]

/-- The conformal factor of a conformal map at some point `x`. Some authors refer to this function
as the characteristic function of the conformal map. -/
def conformalFactorAt {f : E → F} {x : E} (h : ConformalAt f x) : ℝ :=
  Classical.choose (conformalAt_iff'.mp h)

/--
@isnad1 id=lt.1h4v.s6.ed0bf051db67 from=seed src=0 shape=a9e5053e vocab=8d1bb565
-/
theorem conformalFactorAt_pos {f : E → F} {x : E} (h : ConformalAt f x) : 0 < conformalFactorAt h :=
  (Classical.choose_spec <| conformalAt_iff'.mp h).1

/--
@isnad1 id=eq.1h6v.s9.c7fa1ee0ec45 from=seed src=0 shape=10933b66 vocab=bbd5cf6c
-/
theorem conformalFactorAt_inner_eq_mul_inner' {f : E → F} {x : E} (h : ConformalAt f x) (u v : E) :
    ⟪(fderiv ℝ f x) u, (fderiv ℝ f x) v⟫ = (conformalFactorAt h : ℝ) * ⟪u, v⟫ :=
  (Classical.choose_spec <| conformalAt_iff'.mp h).2 u v

/--
@isnad1 id=eq.2h7v.s9.fac1449821b6 from=seed src=0 shape=c82bd1da vocab=72f5b620
-/
theorem conformalFactorAt_inner_eq_mul_inner {f : E → F} {x : E} {f' : E →L[ℝ] F}
    (h : HasFDerivAt f f' x) (H : ConformalAt f x) (u v : E) :
    ⟪f' u, f' v⟫ = (conformalFactorAt H : ℝ) * ⟪u, v⟫ :=
  H.differentiableAt.hasFDerivAt.unique h ▸ conformalFactorAt_inner_eq_mul_inner' H u v
