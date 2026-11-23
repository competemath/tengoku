/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Tengoku.Leancert.LeanCert.Engine.IntervalEval

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Core Bound Verification

This module provides the fundamental infrastructure for certificate-driven verification of
numerical bounds using interval arithmetic.

## Main definitions

### Boolean Checkers
* `checkUpperBound` - Check if `∀ x ∈ I, f(x) ≤ c` via interval arithmetic
* `checkLowerBound` - Check if `∀ x ∈ I, c ≤ f(x)` via interval arithmetic
* `checkStrictUpperBound` - Check if `∀ x ∈ I, f(x) < c`
* `checkStrictLowerBound` - Check if `∀ x ∈ I, c < f(x)`

### Golden Theorems
* `verify_upper_bound` - Converts `checkUpperBound = true` to semantic proof
* `verify_lower_bound` - Converts `checkLowerBound = true` to semantic proof
* `verify_strict_upper_bound` - Converts `checkStrictUpperBound = true` to semantic proof
* `verify_strict_lower_bound` - Converts `checkStrictLowerBound = true` to semantic proof
-/

open scoped LeanCert.Core.Expr

namespace LeanCert.Validity

open LeanCert.Core
open LeanCert.Engine

/-! ### Boolean Checkers

These are the functions `native_decide` will execute. They return `Bool`, not `Prop`.
-/

/-- Check if an expression is bounded above by `c` on interval `I`.
    Returns `true` iff domain validity holds AND the computed upper bound is ≤ c. -/
def checkUpperBound (e : Expr) (I : IntervalRat) (c : ℚ) (cfg : EvalConfig) : Bool :=
  checkDomainValid1 e I cfg && decide ((LeanCert.Internal.Rational.evalTotalCore1 e I cfg).hi ≤ c)

/-- Check if an expression is bounded below by `c` on interval `I`.
    Returns `true` iff domain validity holds AND the computed lower bound is ≥ c. -/
def checkLowerBound (e : Expr) (I : IntervalRat) (c : ℚ) (cfg : EvalConfig) : Bool :=
  checkDomainValid1 e I cfg && decide (c ≤ (LeanCert.Internal.Rational.evalTotalCore1 e I cfg).lo)

/-- Check if an expression is strictly bounded above by `c` on interval `I`.
    Returns `true` iff domain validity holds AND the computed upper bound is < c. -/
def checkStrictUpperBound (e : Expr) (I : IntervalRat) (c : ℚ) (cfg : EvalConfig) : Bool :=
  checkDomainValid1 e I cfg && decide ((LeanCert.Internal.Rational.evalTotalCore1 e I cfg).hi < c)

/-- Check if an expression is strictly bounded below by `c` on interval `I`.
    Returns `true` iff domain validity holds AND the computed lower bound is > c. -/
def checkStrictLowerBound (e : Expr) (I : IntervalRat) (c : ℚ) (cfg : EvalConfig) : Bool :=
  checkDomainValid1 e I cfg && decide (c < (LeanCert.Internal.Rational.evalTotalCore1 e I cfg).lo)

/-! ### Golden Theorems

These theorems convert the boolean `true` from the checkers into semantic proofs
about Real numbers. They are the theorems a tactic will `apply`.
-/

/-- **Golden Theorem for Upper Bounds**

    If `checkUpperBound e I c cfg = true`, then `∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c`.
@isnad1 id=le.3h5v.s5.983ec312f879 from=translated src=- shape=bc83ceb3 vocab=346fe84e
-/
theorem verify_upper_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkUpperBound e I c cfg = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c := by
  simp only [checkUpperBound, Bool.and_eq_true, decide_eq_true_eq] at h_cert
  have hdom := checkDomainValid1_correct e I cfg h_cert.1
  have hhi := h_cert.2
  exact exprCore_le_of_interval_hi e hsupp I c cfg hdom hhi

/-- **Golden Theorem for Lower Bounds**

    If `checkLowerBound e I c cfg = true`, then `∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e`.
@isnad1 id=le.3h5v.s5.424eab2253fb from=translated src=- shape=077acda4 vocab=aeeb7573
-/
theorem verify_lower_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkLowerBound e I c cfg = true) :
    ∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e := by
  simp only [checkLowerBound, Bool.and_eq_true, decide_eq_true_eq] at h_cert
  have hdom := checkDomainValid1_correct e I cfg h_cert.1
  have hlo := h_cert.2
  exact exprCore_ge_of_interval_lo e hsupp I c cfg hdom hlo

/-- **Golden Theorem for Strict Upper Bounds**

    If `checkStrictUpperBound e I c cfg = true`, then `∀ x ∈ I, Expr.eval (fun _ => x) e < c`.
@isnad1 id=lt.3h5v.s5.e26410efa04d from=translated src=- shape=bc83ceb3 vocab=8f0fa6f7
-/
theorem verify_strict_upper_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkStrictUpperBound e I c cfg = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e < c := by
  simp only [checkStrictUpperBound, Bool.and_eq_true, decide_eq_true_eq] at h_cert
  have hdom := checkDomainValid1_correct e I cfg h_cert.1
  have hhi := h_cert.2
  exact exprCore_lt_of_interval_hi_lt e hsupp I c cfg hdom hhi

/-- **Golden Theorem for Strict Lower Bounds**

    If `checkStrictLowerBound e I c cfg = true`, then `∀ x ∈ I, c < Expr.eval (fun _ => x) e`.
@isnad1 id=lt.3h5v.s5.62f8c5672b94 from=translated src=- shape=077acda4 vocab=7549f345
-/
theorem verify_strict_lower_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkStrictLowerBound e I c cfg = true) :
    ∀ x ∈ I, c < Expr.eval (fun _ => x) e := by
  simp only [checkStrictLowerBound, Bool.and_eq_true, decide_eq_true_eq] at h_cert
  have hdom := checkDomainValid1_correct e I cfg h_cert.1
  have hlo := h_cert.2
  exact exprCore_gt_of_interval_lo_gt e hsupp I c cfg hdom hlo

/-! ### Convenience lemmas for pointwise bounds -/

/-- Pointwise upper bound: if check passes and x ∈ I, then f(x) ≤ c
@isnad1 id=le.3h5v.s5.f0d877adfaec from=translated src=- shape=3757f286 vocab=346fe84e
-/
theorem verify_upper_bound_pt (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig) (x : ℝ) (hx : x ∈ I)
    (h_cert : checkUpperBound e I c cfg = true) :
    Expr.eval (fun _ => x) e ≤ c :=
  verify_upper_bound e hsupp I c cfg h_cert x hx

/-- Pointwise lower bound: if check passes and x ∈ I, then c ≤ f(x)
@isnad1 id=le.3h5v.s5.58e37ef48639 from=translated src=- shape=372607f5 vocab=aeeb7573
-/
theorem verify_lower_bound_pt (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig) (x : ℝ) (hx : x ∈ I)
    (h_cert : checkLowerBound e I c cfg = true) :
    c ≤ Expr.eval (fun _ => x) e :=
  verify_lower_bound e hsupp I c cfg h_cert x hx

/-! ### Two-sided bounds -/

/-- Check both lower and upper bounds simultaneously -/
def checkBounds (e : Expr) (I : IntervalRat) (lo hi : ℚ) (cfg : EvalConfig) : Bool :=
  checkLowerBound e I lo cfg && checkUpperBound e I hi cfg

/-- Two-sided bound verification: if both checks pass, then lo ≤ f(x) ≤ hi for all x ∈ I
@isnad1 id=and.3h6v.s5.368da0943a66 from=translated src=- shape=ba0f6ad4 vocab=efc8f208
-/
theorem verify_bounds (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (lo hi : ℚ) (cfg : EvalConfig)
    (h_cert : checkBounds e I lo hi cfg = true) :
    ∀ x ∈ I, lo ≤ Expr.eval (fun _ => x) e ∧ Expr.eval (fun _ => x) e ≤ hi := by
  simp only [checkBounds, Bool.and_eq_true] at h_cert
  intro x hx
  exact ⟨verify_lower_bound e hsupp I lo cfg h_cert.1 x hx,
         verify_upper_bound e hsupp I hi cfg h_cert.2 x hx⟩

/-! ### Argmax/Argmin Verification -/

/-- Check that evaluating f at a point x gives a value ≥ c. -/
def checkPointLowerBound (e : Expr) (x c : ℚ) (cfg : EvalConfig) : Bool :=
  let Ipt : IntervalRat := ⟨x, x, le_refl x⟩
  checkDomainValid1 e Ipt cfg && decide (c ≤ (LeanCert.Internal.Rational.evalTotalCore1 e Ipt cfg).lo)

/-- Check that evaluating f at a point x gives a value ≤ c. -/
def checkPointUpperBound (e : Expr) (x c : ℚ) (cfg : EvalConfig) : Bool :=
  let Ipt : IntervalRat := ⟨x, x, le_refl x⟩
  checkDomainValid1 e Ipt cfg && decide ((LeanCert.Internal.Rational.evalTotalCore1 e Ipt cfg).hi ≤ c)

/-- Verify that c ≤ f(x) at a specific point x.
@isnad1 id=le.2h4v.s5.7699f738cac6 from=translated src=- shape=f97c71e6 vocab=159c44fe
-/
theorem verify_point_lower_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (x c : ℚ) (cfg : EvalConfig)
    (h_cert : checkPointLowerBound e x c cfg = true) :
    c ≤ Expr.eval (fun _ => (x : ℝ)) e := by
  simp only [checkPointLowerBound, Bool.and_eq_true, decide_eq_true_eq] at h_cert
  let Ipt : IntervalRat := ⟨x, x, le_refl x⟩
  have hdom := checkDomainValid1_correct e Ipt cfg h_cert.1
  have hlo := h_cert.2
  have hx_mem : (x : ℝ) ∈ Ipt := ⟨le_refl _, le_refl _⟩
  exact exprCore_ge_of_interval_lo e hsupp Ipt c cfg hdom hlo (x : ℝ) hx_mem

/-- Verify that f(x) ≤ c at a specific point x.
@isnad1 id=le.2h4v.s5.4f177e8fe76c from=translated src=- shape=384b4429 vocab=a313b76d
-/
theorem verify_point_upper_bound (e : Expr) (hsupp : ExprSupportedCore e)
    (x c : ℚ) (cfg : EvalConfig)
    (h_cert : checkPointUpperBound e x c cfg = true) :
    Expr.eval (fun _ => (x : ℝ)) e ≤ c := by
  simp only [checkPointUpperBound, Bool.and_eq_true, decide_eq_true_eq] at h_cert
  let Ipt : IntervalRat := ⟨x, x, le_refl x⟩
  have hdom := checkDomainValid1_correct e Ipt cfg h_cert.1
  have hhi := h_cert.2
  have hx_mem : (x : ℝ) ∈ Ipt := ⟨le_refl _, le_refl _⟩
  exact exprCore_le_of_interval_hi e hsupp Ipt c cfg hdom hhi (x : ℝ) hx_mem

/-- **Argmax Verification Theorem**

    Proves `∀ y ∈ I, f(y) ≤ f(x)` (x is a maximizer) by:
    1. Checking that `∀ y ∈ I, f(y) ≤ c` (the max over I is at most c)
    2. Checking that `c ≤ f(x)` (the value at x is at least c)
@isnad1 id=le.5h6v.s6.0eb26650df11 from=translated src=- shape=47c4b0c1 vocab=9295c8f3
-/
theorem verify_argmax (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (x c : ℚ) (cfg : EvalConfig) (_hx : (x : ℝ) ∈ I)
    (h_upper : checkUpperBound e I c cfg = true)
    (h_point : checkPointLowerBound e x c cfg = true) :
    ∀ y ∈ I, Expr.eval (fun _ => y) e ≤ Expr.eval (fun _ => (x : ℝ)) e := by
  intro y hy
  have h1 : Expr.eval (fun _ => y) e ≤ c := verify_upper_bound e hsupp I c cfg h_upper y hy
  have h2 : c ≤ Expr.eval (fun _ => (x : ℝ)) e := verify_point_lower_bound e hsupp x c cfg h_point
  exact le_trans h1 h2

/-- **Argmin Verification Theorem**

    Proves `∀ y ∈ I, f(x) ≤ f(y)` (x is a minimizer).
@isnad1 id=le.5h6v.s6.31642b04a7b3 from=translated src=- shape=c481c359 vocab=91486379
-/
theorem verify_argmin (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (x c : ℚ) (cfg : EvalConfig) (_hx : (x : ℝ) ∈ I)
    (h_lower : checkLowerBound e I c cfg = true)
    (h_point : checkPointUpperBound e x c cfg = true) :
    ∀ y ∈ I, Expr.eval (fun _ => (x : ℝ)) e ≤ Expr.eval (fun _ => y) e := by
  intro y hy
  have h1 : Expr.eval (fun _ => (x : ℝ)) e ≤ c := verify_point_upper_bound e hsupp x c cfg h_point
  have h2 : c ≤ Expr.eval (fun _ => y) e := verify_lower_bound e hsupp I c cfg h_lower y hy
  exact le_trans h1 h2

end LeanCert.Validity
