/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.SecondMoment.Internal

/-!
# Second-moment concentration for local events

Let `Y` count the events `A k`, `k ∈ F`, under a product of probability measures, where
each event depends only on the coordinates in a finite set `S k`, and each `S k` meets at
most `D` of the sets `S l`, `l ∈ F`. Indicators of events with disjoint coordinate sets
are independent, so their covariance vanishes; every other pair has covariance at most
one. Hence `Var Y ≤ |F| D`, and Chebyshev's inequality bounds the probability that `Y`
deviates from its mean `∑ k, P(A k)` by at least `c` by `|F| D / c²`.

Both theorems hold for any product of probability measures on measurable spaces, with
locality expressed by Mathlib's `DependsOn`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian

open MeasureTheory ProbabilityTheory

end Algebraic.Cutwidth.Gaussian
