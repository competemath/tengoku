/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Probability.Exchangeability.Contractability

/-!
# The covariance structure of a contractable L² sequence

This file opens the Layer 3 (L²) lane of the Exchangeability roadmap
(`TauCetiRoadmap/Exchangeability/README.md`, "Layer 3: L² averaging library and the
standard-Borel de Finetti route"), whose first analytic input is the *uniform covariance
structure of a contractable L² sequence* (`contractable_covariance_structure`). It also
supplies the two Layer 3 preliminaries listed before it — "equality of means and integrals
from equal one-dimensional laws" and "equality of pair covariances from equal two-dimensional
laws".

For a real-valued contractable sequence, the one- and two-coordinate `IdentDistrib` facts in
`TauCeti.Probability.Exchangeability.Contractability` give the uniform first- and second-moment
structure:

* `Contractable.integral_coord_eq`: all coordinate means agree;
* `Contractable.variance_coord_eq`: all coordinate variances agree;
* `Contractable.covariance_eq_of_ne`: any two off-diagonal covariances agree,
  `cov[X i, X j; μ] = cov[X k, X l; μ]` for `i ≠ j` and `k ≠ l`.

The `IdentDistrib` and moment machinery is Mathlib's (`ProbabilityTheory.IdentDistrib`,
`ProbabilityTheory.covariance`, `ProbabilityTheory.variance`); the contractability input is
the Layer 0 API in `TauCeti.Probability.Exchangeability.Contractability`. No material from
`cameronfreer/exchangeability` is used: the source's L² lane carries the real-valued
statement through block averages, whereas this file records only the elementary
moment-uniformity that seeds it.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

variable {γ : Type*} [MeasurableSpace γ] [NormedAddCommGroup γ] [NormedSpace ℝ γ]
  [BorelSpace γ] {Z : ℕ → Ω → γ}

section Real

variable {X : ℕ → Ω → ℝ}

end Real

end Probability

end TauCeti
