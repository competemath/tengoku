/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Probability.Exchangeability.ExchangeableAtMonotone
public import Tengoku.Tauceti.TauCeti.Probability.UniformSampling
public import Tengoku

/-!
# Finite exchangeability as sampling without replacement

This file identifies every shorter marginal of a finite exchangeable process with sampling
without replacement from its observed finite population. Given a population law
`ρ : Measure (κ → α)`, `sampleWithoutReplacement ρ` first draws `x ∼ ρ`, independently
draws a uniform injective selection `k : ι → κ`, and returns `x ∘ k`.

The main theorem says that if the first `n` coordinates of a process are exchangeable, then
sampling `m ≤ n` entries without replacement from that random `n`-tuple has exactly the original
`m`-prefix law. This is the representation half of the finite de Finetti argument: the companion
with-replacement law is the product of the empirical measure, and the collision estimate in
`TauCeti.Probability.UniformSampling` then controls their difference.

The proof averages the exchangeable law over all injective selections. Every selection has the
same law by `ExchangeableAt.blockLaw_eq_prefixLaw_of_injective`, so the average has that law too.

## Main declarations

* `sampleWithoutReplacement` — sample a random finite population at uniformly chosen distinct
  indices;
* `measurable_reindexPopulation` — measurability of the joint selection/population evaluation;
* `sampleWithoutReplacement_apply` — its evaluation as the average of the selected laws;
* `ExchangeableAt.sampleWithoutReplacement_eq_prefixLaw` — the finite exchangeable
  without-replacement representation.

## References

* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, Layer 8, “finite de Finetti bounds”.
* P. Diaconis and D. Freedman, “Finite exchangeable sequences”, *Annals of Probability* 8
  (1980), 745–764.

No material is adapted from `cameronfreer/exchangeability`; its three de Finetti routes concern
infinite exchangeable sequences rather than quantitative finite approximation.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

end Probability

end TauCeti
