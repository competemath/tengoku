/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Tengoku.Leancert.LeanCert.Engine.AD
import Tengoku.Leancert.LeanCert.Engine.IntervalEvalReal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Calculus Examples

This file demonstrates automatic differentiation and derivative
bounds using LeanCert.

## Verified AD Examples

The `LeanCert.Engine.evalDualUnchecked_val_correct` theorem is **FULLY PROVED** for the supported
expression subset {const, var, add, mul, neg, sin, cos}. This demonstrates
verified forward-mode automatic differentiation with interval bounds.
-/

open scoped LeanCert.Core.Expr

namespace LeanCert.Examples.Calculus

open LeanCert.Core
open LeanCert.Engine

/-! ### Supported expressions for AD -/

/-- The expression x² -/
def exprXSquared : Expr := Expr.mul (Expr.var 0) (Expr.var 0)

/-- Proof that x² is in the supported subset
@isnad1 id=adsuppor.0h0v.s1.01bebd16ebac from=translated src=- shape=49959d42 vocab=442ac934
-/
theorem exprXSquared_supported : ADSupported exprXSquared :=
  ADSupported.mul (ADSupported.var 0) (ADSupported.var 0)

/-- The expression x³ = x * x * x -/
def exprXCubed : Expr :=
  Expr.mul (Expr.var 0) (Expr.mul (Expr.var 0) (Expr.var 0))

/-- Proof that x³ is supported
@isnad1 id=adsuppor.0h0v.s1.acb8310b9881 from=translated src=- shape=49959d42 vocab=5a9cd2e0
-/
theorem exprXCubed_supported : ADSupported exprXCubed :=
  ADSupported.mul (ADSupported.var 0)
    (ADSupported.mul (ADSupported.var 0) (ADSupported.var 0))

/-- The expression sin(x) * cos(x) -/
def exprSinCos : Expr := Expr.mul (Expr.sin (Expr.var 0)) (Expr.cos (Expr.var 0))

/-- Proof that sin(x)*cos(x) is supported
@isnad1 id=adsuppor.0h0v.s1.e00c33f49b44 from=translated src=- shape=49959d42 vocab=649cb1dd
-/
theorem exprSinCos_supported : ADSupported exprSinCos :=
  ADSupported.mul
    (ADSupported.sin (ADSupported.var 0))
    (ADSupported.cos (ADSupported.var 0))

/-! ### Interval environments for AD -/

/-- Unit interval [0, 1] -/
def I01 : IntervalRat := ⟨0, 1, by norm_num⟩

/-- Create a dual environment for differentiating with respect to x -/
def dualEnv01 : DualEnv := mkDualEnv (fun _ => I01) 0

/-! ### Verified value computation -/

/-- Verified: the value component of dual evaluation is correct.
    For any x ∈ [0,1], the value of x² lies in the computed interval.
    This theorem has NO SORRY.
@isnad1 id=mem.1h1v.s4.25d5f2b859e0 from=translated src=- shape=127f57ae vocab=1287fa5c
-/
theorem xSquared_dual_val_correct (x : ℝ) (hx : x ∈ I01) :
    Expr.eval (fun _ => x) exprXSquared ∈ (LeanCert.Internal.AD.evalUnchecked exprXSquared dualEnv01).val := by
  apply LeanCert.Engine.evalDualUnchecked_val_correct exprXSquared exprXSquared_supported
  intro i
  simp only [dualEnv01, mkDualEnv]
  split_ifs
  · exact hx
  · exact hx

/-- Verified: the value component for x³ is correct
@isnad1 id=mem.1h1v.s4.2d932fc42b2d from=translated src=- shape=127f57ae vocab=c2c43e68
-/
theorem xCubed_dual_val_correct (x : ℝ) (hx : x ∈ I01) :
    Expr.eval (fun _ => x) exprXCubed ∈ (LeanCert.Internal.AD.evalUnchecked exprXCubed dualEnv01).val := by
  apply LeanCert.Engine.evalDualUnchecked_val_correct exprXCubed exprXCubed_supported
  intro i
  simp only [dualEnv01, mkDualEnv]
  split_ifs
  · exact hx
  · exact hx

/-- Verified: the value component for sin(x)*cos(x) is correct
@isnad1 id=mem.1h1v.s4.1f5d923128e8 from=translated src=- shape=127f57ae vocab=ded010f4
-/
theorem sinCos_dual_val_correct (x : ℝ) (hx : x ∈ I01) :
    Expr.eval (fun _ => x) exprSinCos ∈ (LeanCert.Internal.AD.evalUnchecked exprSinCos dualEnv01).val := by
  apply LeanCert.Engine.evalDualUnchecked_val_correct exprSinCos exprSinCos_supported
  intro i
  simp only [dualEnv01, mkDualEnv]
  split_ifs
  · exact hx
  · exact hx

/-! ### Point evaluation examples -/

/-- Evaluate x² at a point with its derivative -/
noncomputable def evalXSquaredAt (q : ℚ) : DualInterval :=
  let I := IntervalRat.singleton q
  evalWithDeriv exprXSquared (fun _ => I) 0

/-! ### Verified exp support via IntervalReal

With the new `IntervalReal` (real-endpoint intervals) and `ExprSupportedExt`,
we can now prove facts about expressions containing exp!
-/

/-- The expression exp(x) -/
def exprExp : Expr := Expr.exp (Expr.var 0)

/-- The expression exp(x²) -/
def exprExpXSquared : Expr := Expr.exp (Expr.mul (Expr.var 0) (Expr.var 0))

/-- Proof that exp(x) is in the extended supported subset
@isnad1 id=exprsupp.0h0v.s1.c072f5733abc from=translated src=- shape=49959d42 vocab=795c8884
-/
theorem exprExp_supportedExt : ExprSupportedExt exprExp :=
  ExprSupportedExt.exp (ExprSupportedExt.var 0)

/-- Proof that exp(x²) is in the extended supported subset
@isnad1 id=exprsupp.0h0v.s1.782b1f33caf3 from=translated src=- shape=49959d42 vocab=39a744e5
-/
theorem exprExpXSquared_supportedExt : ExprSupportedExt exprExpXSquared :=
  ExprSupportedExt.exp
    (ExprSupportedExt.mul (ExprSupportedExt.var 0) (ExprSupportedExt.var 0))

/-- Real-endpoint unit interval [0, 1] -/
noncomputable def I01Real : IntervalReal := ⟨0, 1, by norm_num⟩

/-- Verified: exp(x) on [0, 1] gives a value in the computed interval.
    This theorem has NO SORRY - exp is now fully supported!
@isnad1 id=mem.2h2v.s4.085a4ba45979 from=translated src=- shape=c1a58498 vocab=d47e9060
-/
theorem exp_interval_correct (x : ℝ) (hx : x ∈ I01Real) (J : IntervalReal)
    (hJ : evalIntervalReal1? exprExp I01Real = some J) :
    Expr.eval (fun _ => x) exprExp ∈ J :=
  evalIntervalReal1?_correct exprExp x I01Real J hx hJ

/-- Verified: exp(x²) on [0, 1] gives a value in the computed interval.
    This demonstrates chained exp support!
@isnad1 id=mem.2h2v.s4.818e7cf5ad02 from=translated src=- shape=c1a58498 vocab=f5d4bca7
-/
theorem expXSquared_interval_correct (x : ℝ) (hx : x ∈ I01Real) (J : IntervalReal)
    (hJ : evalIntervalReal1? exprExpXSquared I01Real = some J) :
    Expr.eval (fun _ => x) exprExpXSquared ∈ J :=
  evalIntervalReal1?_correct exprExpXSquared x I01Real J hx hJ

end LeanCert.Examples.Calculus
