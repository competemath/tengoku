/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Tengoku.Leancert.LeanCert.Engine.AD.Computable
import Tengoku.Seed.Topology.Order.Monotone

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Golden Theorems for Monotonicity Verification

This file provides Golden Theorems for proving monotonicity properties of expressions
using automatic differentiation with interval arithmetic.

## Main definitions

### Boolean Checkers
* `checkStrictlyIncreasing` - Check if f'(x) > 0 for all x in I (strictly increasing)
* `checkStrictlyDecreasing` - Check if f'(x) < 0 for all x in I (strictly decreasing)

### Golden Theorems
* `verify_strictly_increasing` - Proves `StrictMonoOn f I` from positive derivative bounds
* `verify_strictly_decreasing` - Proves `StrictAntiOn f I` from negative derivative bounds

## Design

The approach uses automatic differentiation to compute interval bounds on derivatives:
1. Compute `dI := derivIntervalCore e I cfg` (interval containing all derivatives)
2. If `dI.lo > 0`, then f'(x) > 0 for all x ∈ I, so f is strictly increasing
3. If `dI.hi < 0`, then f'(x) < 0 for all x ∈ I, so f is strictly decreasing

The mathematical foundation is the Mean Value Theorem: if f' has consistent sign,
then f is monotonic.

## Usage

```lean
-- Prove exp is strictly increasing on [0, 1]
example : StrictMonoOn (fun x => Real.exp x) (Set.Icc 0 1) :=
  verify_strictly_increasing' Expr.exp.var0 (by decide)
    ⟨0, 1, by norm_num⟩ {} (by native_decide)
```
-/

open scoped LeanCert.Core.Expr

namespace LeanCert.Validity

open LeanCert.Core LeanCert.Engine

/-! ### Boolean Checkers for Monotonicity -/

/-- Check if an expression is strictly increasing on an interval.
    Returns true if the derivative lower bound is strictly positive. -/
def checkStrictlyIncreasing (e : Expr) (I : IntervalRat) (cfg : EvalConfig := {}) : Bool :=
  0 < (derivIntervalCore e I cfg).lo

/-- Check if an expression is strictly decreasing on an interval.
    Returns true if the derivative upper bound is strictly negative. -/
def checkStrictlyDecreasing (e : Expr) (I : IntervalRat) (cfg : EvalConfig := {}) : Bool :=
  (derivIntervalCore e I cfg).hi < 0

/-! ### Golden Theorems for Monotonicity -/

/-- **Golden Theorem for Strictly Increasing Functions**

    If `checkStrictlyIncreasing e I cfg = true`, then the function defined by `e`
    is strictly increasing on `I`.

    This uses the Mean Value Theorem: if f'(x) > 0 for all x in the interior of I,
    then f is strictly monotone on I.
@isnad1 id=strictmo.2h3v.s5.f79bec7a1d78 from=translated src=- shape=326e2d30 vocab=b8ce7df7
-/
theorem verify_strictly_increasing (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (h_check : checkStrictlyIncreasing e I cfg = true) :
    StrictMonoOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc (I.lo : ℝ) I.hi) := by
  simp only [checkStrictlyIncreasing, decide_eq_true_eq] at h_check
  have hpos : 0 < (derivIntervalCore e I cfg).lo := by exact_mod_cast h_check
  exact strictMonoOn_of_derivIntervalCore_pos e hsupp I cfg hpos

/-- **Golden Theorem for Strictly Decreasing Functions**

    If `checkStrictlyDecreasing e I cfg = true`, then the function defined by `e`
    is strictly decreasing on `I`.
@isnad1 id=strictan.2h3v.s5.6ed718b78449 from=translated src=- shape=326e2d30 vocab=13059a40
-/
theorem verify_strictly_decreasing (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (h_check : checkStrictlyDecreasing e I cfg = true) :
    StrictAntiOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc (I.lo : ℝ) I.hi) := by
  simp only [checkStrictlyDecreasing, decide_eq_true_eq] at h_check
  have hneg : (derivIntervalCore e I cfg).hi < 0 := by exact_mod_cast h_check
  exact strictAntiOn_of_derivIntervalCore_neg e hsupp I cfg hneg

/-! ### Alternative Formulations

These theorems provide the monotonicity result in the form
`∀ x y ∈ I, x < y → f(x) < f(y)`, which may be more convenient for some applications. -/

/-- Strictly increasing: x < y implies f(x) < f(y)
@isnad1 id=lt.5h5v.s6.fafdad91c7a2 from=translated src=- shape=1c6bb52f vocab=7e75fe8d
-/
theorem verify_strictly_increasing_lt (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (h_check : checkStrictlyIncreasing e I cfg = true) :
    ∀ x ∈ Set.Icc (I.lo : ℝ) I.hi, ∀ y ∈ Set.Icc (I.lo : ℝ) I.hi,
      x < y → Expr.eval (fun _ => x) e < Expr.eval (fun _ => y) e := by
  have hmono := verify_strictly_increasing e hsupp I cfg h_check
  intro x hx y hy hxy
  exact hmono hx hy hxy

/-- Strictly decreasing: x < y implies f(x) > f(y)
@isnad1 id=lt.5h5v.s6.c0886e0d8bcf from=translated src=- shape=657a1be6 vocab=eef2cb6f
-/
theorem verify_strictly_decreasing_lt (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (h_check : checkStrictlyDecreasing e I cfg = true) :
    ∀ x ∈ Set.Icc (I.lo : ℝ) I.hi, ∀ y ∈ Set.Icc (I.lo : ℝ) I.hi,
      x < y → Expr.eval (fun _ => y) e < Expr.eval (fun _ => x) e := by
  have hmono := verify_strictly_decreasing e hsupp I cfg h_check
  intro x hx y hy hxy
  exact hmono hx hy hxy

/-! ### Weak Monotonicity from Strict Monotonicity

For completeness, we provide theorems that derive weak monotonicity (≤) from
the strict monotonicity checks. -/

/-- Monotone (weak): x ≤ y implies f(x) ≤ f(y)
@isnad1 id=monotone.2h3v.s5.3bbe41e8f67b from=translated src=- shape=326e2d30 vocab=b25f07e7
-/
theorem verify_monotone (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (h_check : checkStrictlyIncreasing e I cfg = true) :
    MonotoneOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc (I.lo : ℝ) I.hi) := by
  have hstrict := verify_strictly_increasing e hsupp I cfg h_check
  exact hstrict.monotoneOn

/-- Antitone (weak): x ≤ y implies f(x) ≥ f(y)
@isnad1 id=antitone.2h3v.s5.4fe06ae3bf0e from=translated src=- shape=326e2d30 vocab=405d3bad
-/
theorem verify_antitone (e : Expr) (hsupp : ADSupported e)
    (I : IntervalRat) (cfg : EvalConfig)
    (h_check : checkStrictlyDecreasing e I cfg = true) :
    AntitoneOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc (I.lo : ℝ) I.hi) := by
  have hstrict := verify_strictly_decreasing e hsupp I cfg h_check
  exact hstrict.antitoneOn

/-! ### Convenience Versions with Rational Endpoints

These versions take rational endpoints directly, avoiding the need to construct
an IntervalRat explicitly. -/

/-- Convenience version with explicit rational endpoints
@isnad1 id=strictmo.3h4v.s5.3b3d2d4129b6 from=translated src=- shape=3aeed6e8 vocab=cae12fc9
-/
theorem verify_strictly_increasing_rat (e : Expr) (hsupp : ADSupported e)
    (lo hi : ℚ) (hle : lo ≤ hi) (cfg : EvalConfig)
    (h_check : checkStrictlyIncreasing e ⟨lo, hi, hle⟩ cfg = true) :
    StrictMonoOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc (lo : ℝ) hi) :=
  verify_strictly_increasing e hsupp ⟨lo, hi, hle⟩ cfg h_check

/-- Convenience version with explicit rational endpoints
@isnad1 id=strictan.3h4v.s5.a5ccb4fa5d6a from=translated src=- shape=3aeed6e8 vocab=4267593c
-/
theorem verify_strictly_decreasing_rat (e : Expr) (hsupp : ADSupported e)
    (lo hi : ℚ) (hle : lo ≤ hi) (cfg : EvalConfig)
    (h_check : checkStrictlyDecreasing e ⟨lo, hi, hle⟩ cfg = true) :
    StrictAntiOn (fun x => Expr.eval (fun _ => x) e) (Set.Icc (lo : ℝ) hi) :=
  verify_strictly_decreasing e hsupp ⟨lo, hi, hle⟩ cfg h_check

end LeanCert.Validity
