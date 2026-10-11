/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Tengoku.Causalean.Causalean.Mathlib.Probability.BernoulliMeasure

/-!
# Bernoulli enumeration for occupancy-weighted design factors

This module turns weighted sums over finite Boolean assignments into binomial
sums and controls the inverse-arm contribution of one occupied group. It is
entirely algebraic and does not use conditional probability.
-/

@[expose] public section

namespace Causalean.Stat

open scoped BigOperators
open Causalean.Mathlib.Probability

/-- Given [a total count](hyp:m) and [a success count](hyp:j), [the two-arm inverse-count
contribution](goal) is the sum of the reciprocal success and failure counts when both counts are
positive, and is zero when either count is zero. -/
noncomputable def inverseTwoCounts (m j : Nat) : Real :=
  if 0 < j ∧ j < m then
    (j : Real)⁻¹ + ((m - j : Nat) : Real)⁻¹
  else 0

/-- Given [a total count](hyp:m) and [a success count](hyp:j), [the binomial interior
indicator](goal) equals one when both the success and failure counts are positive, and equals zero
when either count is zero. -/
def interiorIndicator (m j : Nat) : Real :=
  if 0 < j ∧ j < m then 1 else 0

end Causalean.Stat
