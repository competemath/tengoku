/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku

/-!
# A quantitative smooth transition profile

This file records the one-dimensional profile used by the ball and space-time
cutoff constructions.

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. The namespace and imports are independent.

## Main definitions

* `CKN.smoothTransitionProfile`: the canonical smooth transition from `0` to
  `1`.
* `CKN.smoothTransitionProfile.derivBound`: its explicit first-derivative
  bound.

## Main results

* `smoothTransitionProfile.abs_deriv_le_eight`: the first derivative is
  bounded by `8`.
-/

@[expose] public section

noncomputable section

open Polynomial

namespace CKN

/-- The canonical smooth transition from `0` to `1`. -/
def smoothTransitionProfile : ℝ → ℝ :=
  Real.smoothTransition

namespace smoothTransitionProfile

/-- The canonical transition profile is smooth to every order. -/
theorem smooth : ContDiff ℝ (⊤ : ℕ∞) smoothTransitionProfile :=
  Real.smoothTransition.contDiff

/-- The canonical transition profile vanishes to the left of `0`. -/
theorem zero_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    smoothTransitionProfile t = 0 :=
  Real.smoothTransition.zero_of_nonpos ht

/-- The canonical transition profile equals `1` to the right of `1`. -/
theorem one_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    smoothTransitionProfile t = 1 :=
  Real.smoothTransition.one_of_one_le ht

/-- The canonical transition profile is nonnegative. -/
theorem nonneg (t : ℝ) :
    0 ≤ smoothTransitionProfile t :=
  Real.smoothTransition.nonneg t

/-- The canonical transition profile is at most `1`. -/
theorem le_one (t : ℝ) :
    smoothTransitionProfile t ≤ 1 :=
  Real.smoothTransition.le_one t

/-- The explicit first-derivative constant for the canonical transition. -/
def derivBound : ℝ :=
  8

@[simp]
theorem derivBound_eq_eight :
    derivBound = 8 :=
  rfl

end smoothTransitionProfile

end CKN
