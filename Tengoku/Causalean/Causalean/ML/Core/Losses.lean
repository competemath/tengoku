/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Tengoku

/-! # Loss functions for the standalone ML module

This file collects the elementary pointwise loss functions used throughout
`Causalean.ML`: squared loss for regression, Boolean-to-real encoding, softplus,
and score-space logistic loss for binary classification. Logistic models use
Mathlib's canonical `Real.sigmoid`. Everything here is causal-free real
analysis; no probability or causal layer is imported.
-/

@[expose] public section

namespace Causalean.ML

/-- [Squared loss](goal) measures [a real-valued prediction](hyp:ŷ) against
[the observed outcome](hyp:y) by [squaring their difference](step:1).

It measures prediction error by its square. -/
def squaredLoss (ŷ y : ℝ) : ℝ := (y - ŷ) ^ 2

/-- [The zero--one real encoding](goal) makes [a Boolean label](hyp:b) available to real-valued
loss formulas by [mapping true to one and false to zero](step:1).

This lets real-valued loss formulas use binary labels. -/
def bool01 (b : Bool) : ℝ := if b then 1 else 0

/-- [Softplus](goal) turns [an unrestricted real score](hyp:t) into
[the log of one plus its exponential](step:1), a smooth positive quantity used in logistic loss.

It is a smooth positive transformation used to express logistic losses in score space. -/
noncomputable def softplus (t : ℝ) : ℝ := Real.log (1 + Real.exp t)

/-- [The score-space logistic loss](goal) evaluates [a binary outcome](hyp:y) at
[an unrestricted prediction score](hyp:t) as
[softplus minus the zero--one label times the score](step:1).

This is binary cross-entropy written as a function of an unrestricted prediction score. -/
noncomputable def logisticScoreLoss (y : Bool) (t : ℝ) : ℝ :=
  softplus t - bool01 y * t

/-- [A true Boolean label is encoded as the real number one](goal).
@isnad1 id=eq.0h0v.s3.35f8f071e347 from=translated src=- shape=b0ae1d2b vocab=c0ceea22
-/
@[simp] lemma bool01_true : bool01 true = 1 := rfl

/-- A false Boolean label is encoded as zero.
@isnad1 id=eq.0h0v.s3.cb0e4144b13c from=translated src=- shape=b0ae1d2b vocab=e1558fee
-/
@[simp] lemma bool01_false : bool01 false = 0 := rfl

/-- The zero-one encoding of a Boolean label is always nonnegative.
@isnad1 id=le.0h1v.s3.ffb6ad9ff3b4 from=translated src=- shape=b9369acb vocab=389ffc70
-/
lemma bool01_nonneg (b : Bool) : 0 ≤ bool01 b := by
  cases b <;> simp [bool01]

/-- The zero-one encoding of a Boolean label is always at most one.
@isnad1 id=le.0h1v.s3.aab04d23fab3 from=translated src=- shape=a311c14d vocab=389ffc70
-/
lemma bool01_le_one (b : Bool) : bool01 b ≤ 1 := by
  cases b <;> simp [bool01]

/-- [Squared prediction error cannot be negative](goal), regardless of
[the predicted and observed values](hyp:ŷ,y).
@isnad1 id=le.0h2v.s4.ad7df7791695 from=translated src=- shape=a120b2a8 vocab=2e590d16
-/
lemma squaredLoss_nonneg (ŷ y : ℝ) : 0 ≤ squaredLoss ŷ y := sq_nonneg _

/-- Softplus is strictly positive at every score.
@isnad1 id=lt.0h1v.s3.6265ac088ddf from=translated src=- shape=8a62b088 vocab=2fa25e8f
-/
lemma softplus_pos (t : ℝ) : 0 < softplus t := by
  have hpos : (0 : ℝ) < Real.exp t := Real.exp_pos _
  have h1 : (1 : ℝ) < 1 + Real.exp t := by linarith
  exact Real.log_pos h1

end Causalean.ML
