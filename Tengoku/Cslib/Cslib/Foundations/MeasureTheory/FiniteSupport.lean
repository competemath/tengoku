/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Thomas Waring
-/

module

public import Tengoku.Cslib.Cslib.Init
public import Tengoku.Seed.MeasureTheory.Constructions.Pi
public import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Measures supported on finite sets

For a measure that vanishes off a finite set, every set is null-measurable if
singletons are measurable. Finite support is preserved by finite products of
finite measures. These facts let sample-complexity arguments in learning
theory measure failure events of *arbitrary* (non-measurable) learners under
finitely supported adversarial distributions.

`HasFiniteSupport` records this property as a typeclass, with an instance for
finite products.

The [PFR project](https://github.com/teorth/pfr/blob/master/PFR/ForMathlib/Entropy/Measure.lean)
has an equivalent `ProbabilityTheory.FiniteSupport` class, expressed using an almost-everywhere
`Finset` witness.

## Main statements

- `MeasureTheory.HasFiniteSupport`: a measure vanishes off some finite set.
- `MeasureTheory.HasFiniteSupport.exists_eq_sum_smul_dirac`: on a space with measurable
  singletons, a measure with finite support is a finite sum of Dirac measures weighted by
  its singleton masses.
- `MeasureTheory.HasFiniteSupport.isFiniteMeasure`: a sigma-finite measure with finite
  support is finite.
- `MeasureTheory.NullMeasurableSet.of_hasFiniteSupport`: on a space with measurable
  singletons, every set is null-measurable for a measure with finite support,
  including finite products.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace MeasureTheory

/-- A measure vanishes off a finite set.-/
class HasFiniteSupport {α : Type*} [MeasurableSpace α] (μ : Measure α) : Prop where
  /-- Some finite set has null complement.-/
  exists_finite_measure_compl_zero : ∃ s : Set α, s.Finite ∧ μ sᶜ = 0

/-- On a space with measurable singletons, a measure with finite support is a finite sum
of Dirac measures weighted by its singleton masses. This is `Measure.ae_mem_finset_iff`
applied to a finite support.
@isnad1 id=ex.0h2v.s6.d1c6c96c9763 from=translated src=- shape=24e39f71 vocab=3c5ad10e
-/
theorem HasFiniteSupport.exists_eq_sum_smul_dirac {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [HasFiniteSupport μ] :
    ∃ s : Finset α, μ = ∑ a ∈ s, μ {a} • Measure.dirac a := by
  obtain ⟨s, hs, hμ⟩ := HasFiniteSupport.exists_finite_measure_compl_zero (μ := μ)
  refine ⟨hs.toFinset, Measure.ae_mem_finset_iff.mp ?_⟩
  change μ (hs.toFinset : Set α)ᶜ = 0
  simpa using hμ

/-- On a space with measurable singletons, every set is null-measurable for a measure
with finite support.
@isnad1 id=nullmeas.0h3v.s4.a7941f6bd722 from=translated src=- shape=8338a329 vocab=b39ceecb
-/
theorem NullMeasurableSet.of_hasFiniteSupport {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] {μ : Measure α} [HasFiniteSupport μ]
    (t : Set α) : NullMeasurableSet t μ := by
  obtain ⟨s, hs, hμ⟩ := HasFiniteSupport.exists_finite_measure_compl_zero (μ := μ)
  rw [← inter_union_sdiff t s]
  exact (hs.subset inter_subset_right).measurableSet.nullMeasurableSet.union_null
    (measure_mono_null (sdiff_subset_compl t s) hμ)

end MeasureTheory
