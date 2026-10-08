/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Edge.Exact
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Edge.Decay.Internal

/-!
# Threshold decay of Gaussian crossings

A threshold `t` separates two unit Gaussian forms with correlation `ρ` with probability at
most `exp (-t²/2) · arccos ρ / π`. This multiplies Sheppard's bound
`gaussPi_between_le_arccos` by the Gaussian factor `exp (-t²/2)`, so thresholds far from
the median are crossed rarely.

* `prod_gaussianReal_abs_sub_le_abs_exp`: for independent centered Gaussians `X` and `Y` of
  variances `s > 0` and `r`, the event `|X - c| ≤ |Y|` has probability at most
  `(2/π) arctan (√r / √s) exp (-c² / (2 (s + r)))`. In polar coordinates the event occupies,
  at each radius `R`, at most two arcs of total length `4 arctan (√r / √s)`, and none when
  `R < |c| / √(s + r)`; the radial tail beyond that radius carries the factor
  `exp (-c² / (2 (s + r)))`.
* `gaussPi_between_le_arctan_exp`: for coefficient vectors of equal norm with nonzero sum, a
  threshold `t` separates the two forms with probability at most
  `(2/π) arctan (‖β - α‖ / ‖α + β‖) exp (-t² / (2 ‖α‖²))`. The forms `form (α + β)` and
  `form (β - α)` are independent, and a crossing forces the first to lie within the
  absolute value of the second around `2t`.
* `gaussPi_between_le_exp_arccos`: the bound `exp (-t²/2) arccos ρ / π` for unit forms.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian

open MeasureTheory ProbabilityTheory
open scoped NNReal

end Algebraic.Cutwidth.Gaussian
