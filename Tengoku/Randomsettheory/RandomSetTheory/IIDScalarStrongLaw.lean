/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Seed.Probability.StrongLaw
import Tengoku.Seed.MeasureTheory.Function.ConvergenceInMeasure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Scalar empirical averages of i.i.d. observations

This module provides a small reusable interface from an i.i.d. sample in an
arbitrary measurable observation space to the scalar strong law.  It derives
independence and identical distribution of a measurable scalar observable by
composition, then records both almost-everywhere and in-measure convergence.

No random-set-specific or application-specific object occurs in the API.
-/

open Filter MeasureTheory
open scoped BigOperators Function Topology

noncomputable section

namespace ProbabilityTheory

variable {Omega Sample : Type*} [MeasurableSpace Omega]
  [MeasurableSpace Sample] {probabilityMeasure : Measure Omega}

/-- Scalar empirical average, with the value at sample size zero inherited
from division in `Real`.  This is the normalization used by `strong_law_ae_real`.-/
def scalarEmpiricalAverage (X : Nat → Omega → Real) (n : Nat)
    (omega : Omega) : Real :=
  (∑ i ∈ Finset.range n, X i omega) / n

/-- Almost-everywhere scalar strong law for a measurable observable of
pairwise independent identically distributed observations.-/
theorem ae_tendsto_scalarEmpiricalAverage_iid
    (observation : Nat → Omega → Sample) (f : Sample → Real)
    (hf : Measurable f)
    (hintegrable : Integrable (f ∘ observation 0) probabilityMeasure)
    (hindep : Pairwise ((· ⟂ᵢ[probabilityMeasure] ·) on observation))
    (hident : ∀ i, IdentDistrib (observation i) (observation 0)
      probabilityMeasure probabilityMeasure) :
    ∀ᵐ omega ∂probabilityMeasure,
      Tendsto
        (fun n : Nat ↦
          scalarEmpiricalAverage (fun i ↦ f ∘ observation i) n omega)
        atTop
        (nhds (∫ omega, f (observation 0 omega) ∂probabilityMeasure)) := by
  let X : Nat → Omega → Real := fun i ↦ f ∘ observation i
  have hXident : ∀ i, IdentDistrib (X i) (X 0)
      probabilityMeasure probabilityMeasure := fun i ↦ (hident i).comp hf
  simpa only [scalarEmpiricalAverage, X, Function.comp_apply] using
    (strong_law_ae_real X hintegrable
      (fun i j hij ↦ (hindep hij).comp hf hf) hXident)

/-- Convergence in measure of the scalar empirical average.  Finite measure is
the only extra assumption needed to pass from the almost-everywhere strong law
to convergence in measure.-/
theorem tendstoInMeasure_scalarEmpiricalAverage_iid
    [IsFiniteMeasure probabilityMeasure]
    (observation : Nat → Omega → Sample) (f : Sample → Real)
    (hf : Measurable f)
    (hintegrable : Integrable (f ∘ observation 0) probabilityMeasure)
    (hindep : Pairwise ((· ⟂ᵢ[probabilityMeasure] ·) on observation))
    (hident : ∀ i, IdentDistrib (observation i) (observation 0)
      probabilityMeasure probabilityMeasure) :
    TendstoInMeasure probabilityMeasure
      (fun n ↦ scalarEmpiricalAverage (fun i ↦ f ∘ observation i) n)
      atTop (fun _ ↦ ∫ omega, f (observation 0 omega) ∂probabilityMeasure) := by
  let X : Nat → Omega → Real := fun i ↦ f ∘ observation i
  have hXident : ∀ i, IdentDistrib (X i) (X 0)
      probabilityMeasure probabilityMeasure := fun i ↦ (hident i).comp hf
  have hXintegrable : ∀ i, Integrable (X i) probabilityMeasure :=
    fun i ↦ (hXident i).integrable_iff.mpr hintegrable
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    exact ((integrable_finsetSum (Finset.range n)
      (fun i _hi ↦ hXintegrable i)).div_const (n : Real)).aestronglyMeasurable
  · simpa only [X] using
      (ae_tendsto_scalarEmpiricalAverage_iid observation f hf hintegrable
        hindep hident)

end ProbabilityTheory
