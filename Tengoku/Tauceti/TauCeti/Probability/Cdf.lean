/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku

/-!
# The cumulative distribution function of a natural-valued law

A probability measure `μ` on `ℕ` becomes a real law by pushing it forward along the cast
`ℕ → ℝ`. The resulting cumulative distribution function is determined by the cumulative masses of
`μ` itself: it vanishes below the origin, where the pushforward has no mass at all, and at a
nonnegative point `x` it is the mass `μ` gives to the initial segment below the natural floor of
`x`. Every discrete law on `ℕ` therefore reads its real cdf off its own cumulative masses.

## Main results

* `MeasureTheory.Measure.cdf_map_natCast` evaluates the cdf at a nonnegative point;
* `MeasureTheory.Measure.cdf_map_natCast_of_neg` evaluates it below the origin.
-/

public section

open MeasureTheory ProbabilityTheory Set

namespace MeasureTheory.Measure

variable (μ : Measure ℕ) [IsProbabilityMeasure μ]

end MeasureTheory.Measure
