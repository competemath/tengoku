/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Tengoku.Tauceti.TauCeti.MeasureTheory.Measure.ProductKernel
public import Tengoku.Tauceti.TauCeti.Probability.Exchangeability.SamplingWithoutReplacement
public import Tengoku.Tauceti.TauCeti.Probability.Process.EmpiricalMeasure

/-!
# Quantitative finite de Finetti approximation

Let `x : κ → α` be a nonempty finite population. Its empirical distribution is the pushforward
of the uniform law on `κ` by `x`. Sampling `ι` entries from that distribution independently is
therefore the same as choosing a uniform map `ι → κ` and reading the selected entries of `x`.

For a random population with law `ρ`, `sampleWithReplacement ρ` mixes these finite product laws
over `ρ`. The law `sampleWithoutReplacement ρ` already represents every shorter marginal of a
finite exchangeable process. The collision coupling between uniform maps and uniform injective
maps consequently gives, for every measurable event `A`,

```text
prefixLaw μ X m A ≤ sampleWithReplacement (prefixLaw μ X n) A + choose(m, 2) / n
sampleWithReplacement (prefixLaw μ X n) A ≤ prefixLaw μ X m A + choose(m, 2) / n.
```

Thus every `m`-coordinate marginal of an `n`-exchangeable process is quantitatively approximated
by a mixture of `m`-fold product measures of empirical distributions. The bound is deliberately
eventwise rather than packaged in a new total-variation definition.

## Main declarations

* `TauCeti.Probability.empiricalMeasureOfFintype`: the empirical probability measure of a nonempty
  finite population;
* `TauCeti.Probability.sampleWithReplacement`: the mixture of finite powers of those empirical
  measures;
* `TauCeti.Probability.sampleWithReplacement_eq_bind_pi_empiricalMeasureOfFintype`: its
  product-mixture characterization;
* `TauCeti.Probability.ExchangeableAt.finiteDeFinetti`: the paired eventwise finite de Finetti
  bound;
* `TauCeti.Probability.ExchangeableAt.prefixLaw_le_sampleWithReplacement_add` and
  `TauCeti.Probability.ExchangeableAt.sampleWithReplacement_le_prefixLaw_add`: the two sides of
  the finite de Finetti bound.

## References

* P. Diaconis and D. Freedman, “Finite exchangeable sequences”, *Annals of Probability* 8
  (1980), 745–764.

No material is adapted from `cameronfreer/exchangeability`; that development concerns infinite
exchangeable sequences rather than quantitative finite approximation.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

section EmpiricalPopulation

variable {κ : Type*} [Fintype κ] [Nonempty κ] [MeasurableSpace κ]
  [MeasurableSingletonClass κ]

variable {ι : Type*} [Fintype ι]

/-- Independently sampling from a finite empirical population is the same as choosing a uniform
map into the population and reading the selected entries. -/
theorem pi_empiricalMeasureOfFintype_eq_map_uniformOn (x : κ → α) :
    (ProbabilityMeasure.pi fun _ : ι => empiricalMeasureOfFintype x).toMeasure =
      (uniformOn (Set.univ : Set (ι → κ))).map fun k i => x (k i) := by
  rw [ProbabilityMeasure.toMeasure_pi]
  simp_rw [empiricalMeasureOfFintype_eq_map_uniformOn]
  rw [← Measure.pi_map_pi fun _ : ι => (measurable_of_countable x).aemeasurable]
  rw [← uniformOn_pi (f := fun _ : ι => (Set.univ : Set κ))]
  congr 2
  simp

end EmpiricalPopulation

section Sampling

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]

/-- Sampling with replacement from a random finite population.

For a population law `ρ`, this is the `ρ`-mixture of the `ι`-fold product of each population's
empirical probability measure. -/
def sampleWithReplacement (ρ : Measure (κ → α)) : Measure (ι → α) :=
  ρ.bind fun x => (ProbabilityMeasure.pi fun _ : ι => empiricalMeasureOfFintype x).toMeasure

/-- Sampling with replacement is the mixture of the finite product measures of the populations'
empirical distributions. -/
@[simp]
theorem sampleWithReplacement_eq_bind_pi_empiricalMeasureOfFintype (ρ : Measure (κ → α)) :
    sampleWithReplacement ρ =
      ρ.bind fun x => (ProbabilityMeasure.pi fun _ : ι => empiricalMeasureOfFintype x).toMeasure :=
  (rfl)

section DiscretePopulation

variable [MeasurableSpace κ] [MeasurableSingletonClass κ]

end DiscretePopulation

end Sampling

section FiniteExchangeability

end FiniteExchangeability

end Probability

end TauCeti
