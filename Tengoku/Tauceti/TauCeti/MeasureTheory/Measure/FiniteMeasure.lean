/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku

/-!
# Finite measures

When the underlying σ-algebra is countably generated, singletons are measurable in
`FiniteMeasure α` and in `ProbabilityMeasure α`.

On a finite measurable space, a probability measure is the sum of its singleton masses.

## Main results

* `MeasureTheory.FiniteMeasure.instMeasurableSingletonClass`
* `MeasureTheory.ProbabilityMeasure.instMeasurableSingletonClass`
* `MeasureTheory.Measure.sum_singleton_eq_one`

## Implementation

The statement is really about *finite* measures; the probability-measure form is the subtype
corollary. Countable generation is exactly what the proof consumes — `StandardBorelSpace α` implies
it, but is stronger than needed.

A countable generating family need not be closed under intersection, so it is replaced by the set
algebra it generates (`MeasureTheory.generateSetAlgebra`), which is still countable, is a π-system,
and generates the same σ-algebra. A finite measure is then pinned down by its values there
(`ext_of_generate_finite`, with `Set.univ` supplied by the algebra), so `{μ}` is the countable
intersection of the equalizers `{ν | ν s = μ s}`. Each equalizer is measurable because evaluation at
a fixed measurable set is.
-/

public section

noncomputable section

open MeasureTheory MeasurableSpace Set

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- The singleton masses of a probability measure on a finite measurable space sum to one. -/
theorem Measure.sum_singleton_eq_one {κ : Type*} [Fintype κ] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] (ν : Measure κ) [IsProbabilityMeasure ν] :
    ∑ k, ν {k} = 1 := by
  rw [sum_measure_singleton, Finset.coe_univ, measure_univ]

end MeasureTheory
