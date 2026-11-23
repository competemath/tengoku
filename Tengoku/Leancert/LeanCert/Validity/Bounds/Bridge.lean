/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Tengoku.Leancert.LeanCert.Validity.Bounds.Smart
import Tengoku.Leancert.LeanCert.Engine.Integrate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Set.Icc Bridge Theorems and Subdivision

This module provides bridge theorems between IntervalRat-based proofs and Set.Icc goals,
as well as subdivision theorems for combining bounds from interval partitions.

## Main definitions

### Set.Icc Bridge Theorems
* `verify_upper_bound_Icc` - Bridge for upper bounds (smart version)
* `verify_lower_bound_Icc` - Bridge for lower bounds (smart version)
* `verify_upper_bound_Icc_core` - Bridge for upper bounds (core version)
* `verify_lower_bound_Icc_core` - Bridge for lower bounds (core version)
* `verify_strict_upper_bound_Icc_core` - Bridge for strict upper bounds
* `verify_strict_lower_bound_Icc_core` - Bridge for strict lower bounds

### Subdivision Theorems
* `verify_upper_bound_split` - Combine upper bounds from two halves
* `verify_lower_bound_split` - Combine lower bounds from two halves
* `verify_strict_upper_bound_split` - Combine strict upper bounds
* `verify_strict_lower_bound_split` - Combine strict lower bounds

### General Split Theorems
* `verify_upper_bound_general_split` - Combine from arbitrary split points
* `verify_lower_bound_general_split` - Combine from arbitrary split points
-/

open scoped LeanCert.Core.Expr

namespace LeanCert.Validity

open LeanCert.Core
open LeanCert.Engine

/-! ### Set.Icc Bridge Theorems

These theorems bridge between IntervalRat-based proofs and Set.Icc goals,
allowing tactics to work with the more natural Set.Icc syntax.
-/

/-- Bridge from IntervalRat proof to Set.Icc upper bound goal
@isnad1 id=le.4h6v.s6.116c5ef839cd from=translated src=- shape=32cba42e vocab=45f7d7c5
-/
theorem verify_upper_bound_Icc (e : Expr) (hsupp : ADSupported e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkUpperBoundSmart e ⟨lo, hi, hle⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  have := verify_upper_bound_smart e hsupp ⟨lo, hi, hle⟩ c cfg h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge from IntervalRat proof to Set.Icc lower bound goal
@isnad1 id=le.4h6v.s6.2cf3ee31c4d0 from=translated src=- shape=ac0dcc35 vocab=d2e29d31
-/
theorem verify_lower_bound_Icc (e : Expr) (hsupp : ADSupported e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkLowerBoundSmart e ⟨lo, hi, hle⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have := verify_lower_bound_smart e hsupp ⟨lo, hi, hle⟩ c cfg h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge from IntervalRat proof to Set.Icc upper bound goal (Core version).
    This version uses ExprSupportedCore and the basic checkUpperBound (no monotonicity).
@isnad1 id=le.4h6v.s6.f02d116f7a70 from=translated src=- shape=32cba42e vocab=1bf21a1b
-/
theorem verify_upper_bound_Icc_core (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkUpperBound e ⟨lo, hi, hle⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  have := verify_upper_bound e hsupp ⟨lo, hi, hle⟩ c cfg h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge from IntervalRat proof to Set.Icc lower bound goal (Core version).
    This version uses ExprSupportedCore and the basic checkLowerBound (no monotonicity).
@isnad1 id=le.4h6v.s6.4aff385bf76a from=translated src=- shape=ac0dcc35 vocab=1e35e727
-/
theorem verify_lower_bound_Icc_core (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkLowerBound e ⟨lo, hi, hle⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have := verify_lower_bound e hsupp ⟨lo, hi, hle⟩ c cfg h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge from IntervalRat proof to Set.Icc strict upper bound goal (Core version).
@isnad1 id=lt.4h6v.s6.3588b2b115cb from=translated src=- shape=b08df11c vocab=1b760dcb
-/
theorem verify_strict_upper_bound_Icc_core (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkStrictUpperBound e ⟨lo, hi, hle⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e < c := by
  intro x hx
  have := verify_strict_upper_bound e hsupp ⟨lo, hi, hle⟩ c cfg h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge from IntervalRat proof to Set.Icc strict lower bound goal (Core version).
@isnad1 id=lt.4h6v.s6.41a4aee4d430 from=translated src=- shape=d61672fb vocab=30b8c705
-/
theorem verify_strict_lower_bound_Icc_core (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_cert : checkStrictLowerBound e ⟨lo, hi, hle⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c < Expr.eval (fun _ => x) e := by
  intro x hx
  have := verify_strict_lower_bound e hsupp ⟨lo, hi, hle⟩ c cfg h_cert
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-! ### Subdivision Theorems

These theorems allow combining bounds from interval subdivisions.
When interval arithmetic gives overly wide bounds, subdividing the domain
and proving bounds on each piece can help.
-/

/-- Combine upper bounds from two halves using splitMid.
    If f ≤ c on both halves, then f ≤ c on the whole interval.
@isnad1 id=le.4h5v.s5.94ab54cb2aff from=translated src=- shape=05309c50 vocab=ce4c8a20
-/
theorem verify_upper_bound_split (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkUpperBound e (splitMid I).1 c cfg = true)
    (h_right : checkUpperBound e (splitMid I).2 c cfg = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  rcases mem_splitMid hx with hL | hR
  · exact verify_upper_bound e hsupp (splitMid I).1 c cfg h_left x hL
  · exact verify_upper_bound e hsupp (splitMid I).2 c cfg h_right x hR

/-- Combine lower bounds from two halves using splitMid.
@isnad1 id=le.4h5v.s5.40095a572861 from=translated src=- shape=12981db0 vocab=799a1599
-/
theorem verify_lower_bound_split (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkLowerBound e (splitMid I).1 c cfg = true)
    (h_right : checkLowerBound e (splitMid I).2 c cfg = true) :
    ∀ x ∈ I, c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  rcases mem_splitMid hx with hL | hR
  · exact verify_lower_bound e hsupp (splitMid I).1 c cfg h_left x hL
  · exact verify_lower_bound e hsupp (splitMid I).2 c cfg h_right x hR

/-- Combine strict upper bounds from two halves.
@isnad1 id=lt.4h5v.s5.60256abb4079 from=translated src=- shape=05309c50 vocab=40da9048
-/
theorem verify_strict_upper_bound_split (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkStrictUpperBound e (splitMid I).1 c cfg = true)
    (h_right : checkStrictUpperBound e (splitMid I).2 c cfg = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e < c := by
  intro x hx
  rcases mem_splitMid hx with hL | hR
  · exact verify_strict_upper_bound e hsupp (splitMid I).1 c cfg h_left x hL
  · exact verify_strict_upper_bound e hsupp (splitMid I).2 c cfg h_right x hR

/-- Combine strict lower bounds from two halves.
@isnad1 id=lt.4h5v.s5.2cb76e74555d from=translated src=- shape=12981db0 vocab=9d950087
-/
theorem verify_strict_lower_bound_split (e : Expr) (hsupp : ExprSupportedCore e)
    (I : IntervalRat) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkStrictLowerBound e (splitMid I).1 c cfg = true)
    (h_right : checkStrictLowerBound e (splitMid I).2 c cfg = true) :
    ∀ x ∈ I, c < Expr.eval (fun _ => x) e := by
  intro x hx
  rcases mem_splitMid hx with hL | hR
  · exact verify_strict_lower_bound e hsupp (splitMid I).1 c cfg h_left x hL
  · exact verify_strict_lower_bound e hsupp (splitMid I).2 c cfg h_right x hR

/-- Bridge from subdivision to Set.Icc upper bound goal.
@isnad1 id=le.5h6v.s6.8e6e24195874 from=translated src=- shape=d788f73e vocab=7b272442
-/
theorem verify_upper_bound_Icc_split (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkUpperBound e (splitMid ⟨lo, hi, hle⟩).1 c cfg = true)
    (h_right : checkUpperBound e (splitMid ⟨lo, hi, hle⟩).2 c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  have := verify_upper_bound_split e hsupp ⟨lo, hi, hle⟩ c cfg h_left h_right
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge from subdivision to Set.Icc lower bound goal.
@isnad1 id=le.5h6v.s6.23875b94a6d0 from=translated src=- shape=c577fb55 vocab=26cdf6cd
-/
theorem verify_lower_bound_Icc_split (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkLowerBound e (splitMid ⟨lo, hi, hle⟩).1 c cfg = true)
    (h_right : checkLowerBound e (splitMid ⟨lo, hi, hle⟩).2 c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  have := verify_lower_bound_split e hsupp ⟨lo, hi, hle⟩ c cfg h_left h_right
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge from subdivision to Set.Icc strict upper bound goal.
@isnad1 id=lt.5h6v.s6.f2da4840f63e from=translated src=- shape=87a3c485 vocab=cfac3017
-/
theorem verify_strict_upper_bound_Icc_split (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkStrictUpperBound e (splitMid ⟨lo, hi, hle⟩).1 c cfg = true)
    (h_right : checkStrictUpperBound e (splitMid ⟨lo, hi, hle⟩).2 c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e < c := by
  intro x hx
  have := verify_strict_upper_bound_split e hsupp ⟨lo, hi, hle⟩ c cfg h_left h_right
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-- Bridge from subdivision to Set.Icc strict lower bound goal.
@isnad1 id=lt.5h6v.s6.6d3dbf8b679a from=translated src=- shape=b3ecaf42 vocab=119b4043
-/
theorem verify_strict_lower_bound_Icc_split (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkStrictLowerBound e (splitMid ⟨lo, hi, hle⟩).1 c cfg = true)
    (h_right : checkStrictLowerBound e (splitMid ⟨lo, hi, hle⟩).2 c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c < Expr.eval (fun _ => x) e := by
  intro x hx
  have := verify_strict_lower_bound_split e hsupp ⟨lo, hi, hle⟩ c cfg h_left h_right
  apply this
  rwa [IntervalRat.mem_iff_mem_Icc]

/-! ### General Split Theorems

These theorems work with arbitrary split points, not just midpoints.
Useful for adaptive subdivision algorithms.
-/

/-- Any x in [lo, hi] is in [lo, mid] or [mid, hi] for any mid in between
@isnad1 id=or.3h4v.s6.437815aab9b3 from=translated src=- shape=30ac50fc vocab=82b05551
-/
theorem mem_split_general {lo mid hi : ℚ} {x : ℝ}
    (hx : x ∈ Set.Icc (lo : ℝ) (hi : ℝ))
    (_hLeMid : lo ≤ mid) (_hMidLe : mid ≤ hi) :
    x ∈ Set.Icc (lo : ℝ) (mid : ℝ) ∨ x ∈ Set.Icc (mid : ℝ) (hi : ℝ) := by
  simp only [Set.mem_Icc] at hx ⊢
  by_cases! h : x ≤ mid
  · left; exact ⟨hx.1, h⟩
  · right
    exact ⟨le_of_lt h, hx.2⟩

/-- Combine already-certified upper bounds on adjacent intervals.  Unlike the
checker-specific theorem below, this supports recursive subdivision proofs.
@isnad1 id=le.5h6v.s6.f527ccd49721 from=translated src=- shape=50e24c82 vocab=41886026
-/
theorem combine_upper_bound_general_split (e : Expr) (lo mid hi c : ℚ)
    (hLo : lo ≤ mid) (hHi : mid ≤ hi)
    (h_left : ∀ x ∈ Set.Icc (lo : ℝ) (mid : ℝ), Expr.eval (fun _ => x) e ≤ c)
    (h_right : ∀ x ∈ Set.Icc (mid : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e ≤ c) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  rcases mem_split_general hx hLo hHi with hL | hR
  · exact h_left x hL
  · exact h_right x hR

/-- Combine already-certified lower bounds on adjacent intervals.
@isnad1 id=le.5h6v.s6.00efdfe7b706 from=translated src=- shape=9d53f2f1 vocab=41886026
-/
theorem combine_lower_bound_general_split (e : Expr) (lo mid hi c : ℚ)
    (hLo : lo ≤ mid) (hHi : mid ≤ hi)
    (h_left : ∀ x ∈ Set.Icc (lo : ℝ) (mid : ℝ), c ≤ Expr.eval (fun _ => x) e)
    (h_right : ∀ x ∈ Set.Icc (mid : ℝ) (hi : ℝ), c ≤ Expr.eval (fun _ => x) e) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  rcases mem_split_general hx hLo hHi with hL | hR
  · exact h_left x hL
  · exact h_right x hR

/-- Combine already-certified strict upper bounds on adjacent intervals.
@isnad1 id=lt.5h6v.s6.5c2b3ec28644 from=translated src=- shape=54dd1ef8 vocab=65128f6d
-/
theorem combine_strict_upper_bound_general_split (e : Expr) (lo mid hi c : ℚ)
    (hLo : lo ≤ mid) (hHi : mid ≤ hi)
    (h_left : ∀ x ∈ Set.Icc (lo : ℝ) (mid : ℝ), Expr.eval (fun _ => x) e < c)
    (h_right : ∀ x ∈ Set.Icc (mid : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e < c) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e < c := by
  intro x hx
  rcases mem_split_general hx hLo hHi with hL | hR
  · exact h_left x hL
  · exact h_right x hR

/-- Combine already-certified strict lower bounds on adjacent intervals.
@isnad1 id=lt.5h6v.s6.abdf9fa5f78d from=translated src=- shape=8cc1aae5 vocab=65128f6d
-/
theorem combine_strict_lower_bound_general_split (e : Expr) (lo mid hi c : ℚ)
    (hLo : lo ≤ mid) (hHi : mid ≤ hi)
    (h_left : ∀ x ∈ Set.Icc (lo : ℝ) (mid : ℝ), c < Expr.eval (fun _ => x) e)
    (h_right : ∀ x ∈ Set.Icc (mid : ℝ) (hi : ℝ), c < Expr.eval (fun _ => x) e) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c < Expr.eval (fun _ => x) e := by
  intro x hx
  rcases mem_split_general hx hLo hHi with hL | hR
  · exact h_left x hL
  · exact h_right x hR

/-- Combine upper bounds from two arbitrary adjacent intervals.
    If f ≤ c on [lo, mid] and f ≤ c on [mid, hi], then f ≤ c on [lo, hi].
@isnad1 id=le.7h7v.s6.4f92ea247f54 from=translated src=- shape=6e80626f vocab=1bf21a1b
-/
theorem verify_upper_bound_general_split (e : Expr) (hsupp : ExprSupportedCore e)
    (lo mid hi : ℚ) (hLo : lo ≤ mid) (hHi : mid ≤ hi) (_hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkUpperBound e ⟨lo, mid, hLo⟩ c cfg = true)
    (h_right : checkUpperBound e ⟨mid, hi, hHi⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e ≤ c := by
  intro x hx
  rcases mem_split_general hx hLo hHi with hL | hR
  · have := verify_upper_bound e hsupp ⟨lo, mid, hLo⟩ c cfg h_left
    apply this; rwa [IntervalRat.mem_iff_mem_Icc]
  · have := verify_upper_bound e hsupp ⟨mid, hi, hHi⟩ c cfg h_right
    apply this; rwa [IntervalRat.mem_iff_mem_Icc]

/-- Combine lower bounds from two arbitrary adjacent intervals.
@isnad1 id=le.7h7v.s6.46f2cbf38111 from=translated src=- shape=2f5c5944 vocab=1e35e727
-/
theorem verify_lower_bound_general_split (e : Expr) (hsupp : ExprSupportedCore e)
    (lo mid hi : ℚ) (hLo : lo ≤ mid) (hHi : mid ≤ hi) (_hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkLowerBound e ⟨lo, mid, hLo⟩ c cfg = true)
    (h_right : checkLowerBound e ⟨mid, hi, hHi⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  rcases mem_split_general hx hLo hHi with hL | hR
  · have := verify_lower_bound e hsupp ⟨lo, mid, hLo⟩ c cfg h_left
    apply this; rwa [IntervalRat.mem_iff_mem_Icc]
  · have := verify_lower_bound e hsupp ⟨mid, hi, hHi⟩ c cfg h_right
    apply this; rwa [IntervalRat.mem_iff_mem_Icc]

/-- Combine strict upper bounds from two arbitrary adjacent intervals.
@isnad1 id=lt.7h7v.s6.f3b55a554ce5 from=translated src=- shape=11574973 vocab=1b760dcb
-/
theorem verify_strict_upper_bound_general_split (e : Expr) (hsupp : ExprSupportedCore e)
    (lo mid hi : ℚ) (hLo : lo ≤ mid) (hHi : mid ≤ hi) (_hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkStrictUpperBound e ⟨lo, mid, hLo⟩ c cfg = true)
    (h_right : checkStrictUpperBound e ⟨mid, hi, hHi⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), Expr.eval (fun _ => x) e < c := by
  intro x hx
  rcases mem_split_general hx hLo hHi with hL | hR
  · have := verify_strict_upper_bound e hsupp ⟨lo, mid, hLo⟩ c cfg h_left
    apply this; rwa [IntervalRat.mem_iff_mem_Icc]
  · have := verify_strict_upper_bound e hsupp ⟨mid, hi, hHi⟩ c cfg h_right
    apply this; rwa [IntervalRat.mem_iff_mem_Icc]

/-- Combine strict lower bounds from two arbitrary adjacent intervals.
@isnad1 id=lt.7h7v.s6.d03c06b17450 from=translated src=- shape=7137a985 vocab=30b8c705
-/
theorem verify_strict_lower_bound_general_split (e : Expr) (hsupp : ExprSupportedCore e)
    (lo mid hi : ℚ) (hLo : lo ≤ mid) (hHi : mid ≤ hi) (_hle : lo ≤ hi) (c : ℚ) (cfg : EvalConfig)
    (h_left : checkStrictLowerBound e ⟨lo, mid, hLo⟩ c cfg = true)
    (h_right : checkStrictLowerBound e ⟨mid, hi, hHi⟩ c cfg = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ), c < Expr.eval (fun _ => x) e := by
  intro x hx
  rcases mem_split_general hx hLo hHi with hL | hR
  · have := verify_strict_lower_bound e hsupp ⟨lo, mid, hLo⟩ c cfg h_left
    apply this; rwa [IntervalRat.mem_iff_mem_Icc]
  · have := verify_strict_lower_bound e hsupp ⟨mid, hi, hHi⟩ c cfg h_right
    apply this; rwa [IntervalRat.mem_iff_mem_Icc]

end LeanCert.Validity
