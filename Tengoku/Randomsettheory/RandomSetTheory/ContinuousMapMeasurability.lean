/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Seed.MeasureTheory.Constructions.Polish.Basic
import Tengoku.Seed.Topology.ContinuousMap.Compact
import Tengoku.Seed.Topology.ContinuousMap.SecondCountableSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Measurability of continuous-function-valued maps

For a compact second-countable domain, the Borel sigma-algebra of the
uniform topology on `C(K, ℝ)` is determined by point evaluations on a
countable dense sequence.  Consequently a continuous-function-valued map is
measurable as soon as all of its point evaluations are measurable.

This elementary interface is useful for random support processes: their
directional measurability is usually immediate, whereas process-level weak
convergence requires measurability with values in a continuous path space.
-/

open MeasureTheory TopologicalSpace

noncomputable section

namespace ProbabilityTheory

variable {Omega K : Type*} [MeasurableSpace Omega]
  [MetricSpace K] [CompactSpace K] [SecondCountableTopology K]
  [Nonempty K]

/-- Evaluation of a continuous function on a fixed countable dense
sequence.-/
def continuousMapDenseEvaluation (K : Type*) [TopologicalSpace K]
    [SeparableSpace K] [Nonempty K] : C(K, ℝ) → (ℕ → ℝ) :=
  fun f n ↦ f (denseSeq K n)

omit [CompactSpace K] in
theorem continuous_continuousMapDenseEvaluation :
    Continuous (continuousMapDenseEvaluation K) := by
  apply continuous_pi
  intro n
  exact continuous_eval_const (denseSeq K n)

omit [CompactSpace K] in
theorem injective_continuousMapDenseEvaluation :
    Function.Injective (continuousMapDenseEvaluation K) := by
  intro f g hfg
  apply DFunLike.ext'
  exact f.continuous.ext_on (denseRange_denseSeq K) g.continuous
    (Set.eqOn_range.mpr hfg)

/-- A map into a continuous path space is measurable when all point
evaluations are measurable.-/
theorem measurable_continuousMap_of_apply
    [MeasurableSpace C(K, ℝ)] [BorelSpace C(K, ℝ)]
    (f : Omega → C(K, ℝ))
    (hf : ∀ x : K, Measurable (fun omega ↦ f omega x)) :
    Measurable f := by
  let e : C(K, ℝ) → (ℕ → ℝ) := continuousMapDenseEvaluation K
  have he : MeasurableEmbedding e :=
    continuous_continuousMapDenseEvaluation.measurableEmbedding
      injective_continuousMapDenseEvaluation
  rw [← he.measurable_comp_iff]
  exact measurable_pi_iff.mpr fun n ↦ hf (denseSeq K n)

/-- Almost-everywhere measurable version of
`measurable_continuousMap_of_apply`.-/
theorem aemeasurable_continuousMap_of_apply
    [MeasurableSpace C(K, ℝ)] [BorelSpace C(K, ℝ)]
    {mu : Measure Omega} (f : Omega → C(K, ℝ))
    (hf : ∀ x : K, AEMeasurable (fun omega ↦ f omega x) mu) :
    AEMeasurable f mu := by
  let e : C(K, ℝ) → (ℕ → ℝ) := continuousMapDenseEvaluation K
  have he : MeasurableEmbedding e :=
    continuous_continuousMapDenseEvaluation.measurableEmbedding
      injective_continuousMapDenseEvaluation
  rw [← he.aemeasurable_comp_iff]
  exact aemeasurable_pi_iff.mpr fun n ↦ hf (denseSeq K n)

end ProbabilityTheory
