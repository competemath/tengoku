/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.NumberTheory.LSeries.WienerIkehara.BoundaryGrowth
import Tengoku.Tauceti.TauCeti.Analysis.Asymptotics.SumWindow
import Tengoku.Tauceti.TauCeti.Analysis.Fourier.Continuous
import Tengoku.Tauceti.TauCeti.Analysis.Fourier.NonnegTestFunction
import Tengoku.Tauceti.TauCeti.NumberTheory.LSeries.Positivity

/-!
# The Chebyshev bound behind Wiener--Ikehara

For nonnegative coefficients `a` whose Dirichlet series has the Wiener--Ikehara boundary data
(summability on `Re s > 1` and a remainder `G = LSeries a - A / (s - 1)` continuous on
`Re s ≥ 1`), the partial sums grow at most linearly:
`∑_{1 ≤ n ≤ t} ‖a n‖ = O(t)`.

This is the Chebyshev-type bound that the Tauberian half of Wiener--Ikehara consumes to control
the tails of its test functions. It is derived from the boundary data and nonnegativity alone,
improving the crude `O(t log t)` bound `TauCeti.LSeries.isBigO_sum_Icc_norm_of_boundary`.

The argument has two steps.

* **A window bound.** Choose a smooth compactly supported test function `psi` whose Fourier
  transform is nonnegative, and at least some `c > 0` on a neighbourhood `|v| < η` of the origin
  (`TauCeti.exists_contDiff_hasCompactSupport_fourier_nonneg`). The smoothed asymptotic
  `TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop_of_nonneg` bounds the Fourier-weighted
  series `∑ a n / n * 𝓕 psi (log (n / x) / 2π)` for large `x`. All of its summands are
  nonnegative, and those with `q x < n ≤ x`, where `q = exp (-π η)`, carry a weight at least
  `c / x`. Hence `∑_{q x < n ≤ x} ‖a n‖ ≤ K x`.
* **Summing the windows.** A window bound with a fixed ratio `q < 1` implies linear growth of the
  partial sums, by peeling off the window `(q x, x]` and recursing on `q x`
  (`TauCeti.isBigO_sum_Icc_of_sum_Ioc_floor_mul_le`).

## Main results

* `TauCeti.LSeries.isBigO_sum_Icc_norm_id_of_boundary`: **the Chebyshev bound**
  `∑_{1 ≤ n ≤ t} ‖a n‖ = O(t)` for nonnegative coefficients with Wiener--Ikehara boundary data.

## References

* J. Korevaar, *Tauberian Theory: A Century of Developments*, Chapter III.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.
-/

public section

open Asymptotics Complex Filter FourierTransform Real Set
open scoped ComplexOrder ContDiff Topology

namespace TauCeti.LSeries

variable {a : ℕ → ℂ} {A : ℂ} {G : ℂ → ℂ}

end TauCeti.LSeries
