/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Probability.Distributions.Multinomial.Basic
public import Tengoku

/-!
# Transforms of the multinomial distribution

For the pushforward of `multinomialMeasure n p` into `EuclideanSpace ℝ ι` along
`multinomialToEuclidean` and a direction `θ`, the directional moment generating function is
finite everywhere and equals
`(∑ i, p i * exp (t * θ i)) ^ n`: the multinomial theorem, with the cell weights tilted by
`exp (t * θ i)`. The cumulant generating function is its real logarithm.

The characteristic function of the Euclidean cast is the corresponding complex multinomial
polynomial, `(∑ i, p i * exp (I * t i)) ^ n`.

A probability vector on `ι` forces `ι` to be nonempty, so the statements need no separate
hypothesis for it beyond the parameter `p`. Every statement holds for `n = 0`
(the law is a Dirac mass at zero, and the formula is `1`) and for probability vectors with zero
cells, which contribute nothing to the tilted sum.

## Main results

* `TauCeti.Probability.integrableExpSet_multinomialMeasure` — every real observable has full
  exponential integrability domain, and `TauCeti.Probability.integrableExpSet_inner_multinomial`
  for every direction of the Euclidean pushforward;
* `TauCeti.Probability.mgf_inner_multinomial` — the directional moment generating function;
* `TauCeti.Probability.cgf_inner_multinomial` — the directional cumulant generating function.
* `TauCeti.Probability.charFun_map_multinomialToEuclidean_multinomialMeasure` — the
  characteristic function of the Euclidean cast.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley, 1997,
  Chapter 35.
-/

public section

noncomputable section

open Convexity MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {ι : Type*} [Fintype ι]

/-- The cell weights tilted by `exp (t * θ i)`, as a nonnegative family. -/
private def tiltedWeights (p : ι → NNReal) (θ : ι → ℝ) (t : ℝ) (i : ι) : NNReal :=
  p i * ⟨exp (t * θ i), (exp_pos _).le⟩

/-- Every real observable of a multinomial law has full exponential-integrability domain: the law
has finite support. -/
theorem integrableExpSet_multinomialMeasure (n : ℕ) (p : StdSimplex NNReal ι)
    (f : (ι → ℕ) → ℝ) : integrableExpSet f (multinomialMeasure n p) = Set.univ :=
  Set.eq_univ_of_forall fun _ => integrable_multinomialMeasure _ n p

end Probability

end TauCeti
