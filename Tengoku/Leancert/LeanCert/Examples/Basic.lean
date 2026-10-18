/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Tengoku.Leancert.LeanCert.Engine.IntervalEval
import Tengoku.Leancert.LeanCert.Engine.AD

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Basic Examples

This file demonstrates LeanCert's verified interval arithmetic core.

All examples in this file use only the fully-verified subset of expressions:
const, var, add, mul, neg, sin, cos

The correctness theorems (evalInterval_correct, evalDual_val_correct) are
FULLY PROVED with no sorry, no axioms for this subset.
-/

open scoped LeanCert.Core.Expr

namespace LeanCert.Examples.Basic

open LeanCert.Core
open LeanCert.Engine

/-! ### Building supported expressions -/

/-- The expression x² (x squared) -/
def xSq : Expr := Expr.mul (Expr.var 0) (Expr.var 0)

/-- Proof that x² is in the supported subset -/
theorem xSq_supported : ADSupported xSq :=
  ADSupported.mul (ADSupported.var 0) (ADSupported.var 0)

/-- The expression x² + 2x + 1 = (x + 1)² -/
def exprSquare : Expr :=
  Expr.add (Expr.add (Expr.mul (Expr.var 0) (Expr.var 0))
                     (Expr.mul (Expr.const 2) (Expr.var 0)))
           (Expr.const 1)

/-- Proof that x² + 2x + 1 is in the supported subset -/
theorem exprSquare_supported : ADSupported exprSquare :=
  ADSupported.add
    (ADSupported.add
      (ADSupported.mul (ADSupported.var 0) (ADSupported.var 0))
      (ADSupported.mul (ADSupported.const 2) (ADSupported.var 0)))
    (ADSupported.const 1)

/-- The expression sin(x) + cos(x) -/
def exprSinCos : Expr :=
  Expr.add (Expr.sin (Expr.var 0)) (Expr.cos (Expr.var 0))

/-- Proof that sin(x) + cos(x) is in the supported subset -/
theorem exprSinCos_supported : ADSupported exprSinCos :=
  ADSupported.add
    (ADSupported.sin (ADSupported.var 0))
    (ADSupported.cos (ADSupported.var 0))

/-! ### Interval construction -/

/-- The unit interval [0, 1] -/
def I01 : IntervalRat := ⟨0, 1, by norm_num⟩

/-- The interval [-1, 1] -/
def symInterval : IntervalRat := ⟨-1, 1, by norm_num⟩

/-- A small interval around 0: [-1/10, 1/10] -/
def smallInterval : IntervalRat := ⟨-1/10, 1/10, by norm_num⟩

/-! ### Interval membership examples -/

/-! ### Expression evaluation examples -/

/-! ### Verified interval evaluation -/

/-! ### Using smart constructors -/

/-- Build x² using smart constructors that carry the support proof -/
def xSq' : { e : Expr // ADSupported e } :=
  mkMul (mkVar 0) (mkVar 0)

/-! ### Multi-variable example -/

/-- The expression x * y (product of two variables) -/
def exprXY : Expr := Expr.mul (Expr.var 0) (Expr.var 1)

theorem exprXY_supported : ADSupported exprXY :=
  ADSupported.mul (ADSupported.var 0) (ADSupported.var 1)

/-- Multi-variable interval environment -/
def ρ_xy : IntervalEnv := fun i => if i = 0 then I01 else symInterval

end LeanCert.Examples.Basic
