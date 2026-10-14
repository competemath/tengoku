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

/-- The canonical transition profile is smooth to every order.
@isnad1 id=contdiff.0h0v.s5.d90d7f7023bd from=translated src=- shape=3cea26be vocab=d59d90d1
-/
theorem smooth : ContDiff ℝ (⊤ : ℕ∞) smoothTransitionProfile :=
  Real.smoothTransition.contDiff

/-- The canonical transition profile vanishes to the left of `0`.
@isnad1 id=eq.1h1v.s4.592873e02017 from=translated src=- shape=278e0375 vocab=3321799c
-/
theorem zero_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    smoothTransitionProfile t = 0 :=
  Real.smoothTransition.zero_of_nonpos ht

/-- The canonical transition profile equals `1` to the right of `1`.
@isnad1 id=eq.1h1v.s4.529d21be0f41 from=translated src=- shape=97c35add vocab=3321799c
-/
theorem one_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    smoothTransitionProfile t = 1 :=
  Real.smoothTransition.one_of_one_le ht

/-- The canonical transition profile is nonnegative.
@isnad1 id=le.0h1v.s3.0c1379d8ec2c from=translated src=- shape=8a62b088 vocab=3321799c
-/
theorem nonneg (t : ℝ) :
    0 ≤ smoothTransitionProfile t :=
  Real.smoothTransition.nonneg t

/-- The canonical transition profile is at most `1`.
@isnad1 id=le.0h1v.s3.be80018368f0 from=translated src=- shape=b14ee516 vocab=3321799c
-/
theorem le_one (t : ℝ) :
    smoothTransitionProfile t ≤ 1 :=
  Real.smoothTransition.le_one t

/-- The explicit first-derivative constant for the canonical transition. -/
def derivBound : ℝ :=
  8

/--
@isnad1 id=eq.0h0v.s3.a2effbf094f2 from=translated src=- shape=ffdda526 vocab=07a7be58
-/
@[simp]
theorem derivBound_eq_eight :
    derivBound = 8 :=
  rfl

end smoothTransitionProfile

end CKN
