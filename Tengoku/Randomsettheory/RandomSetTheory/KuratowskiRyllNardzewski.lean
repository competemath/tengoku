/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.MeasurableSelection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Kuratowski--Ryll-Nardzewski measurable selection theorem

We construct coherent approximate selections at geometric accuracies.  Each
new correspondence is restricted to an open ball around the preceding
countably-valued selection, hence remains Effros measurable.  The successive
distances are summable; completeness gives a pointwise limit, and closedness
of the values turns that limit into an exact measurable selection.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Set Metric MeasureTheory TopologicalSpace Filter
open scoped Topology

noncomputable section

namespace RandomSetTheory

/-- Geometric accuracy used in the selection construction.-/
def selectionAccuracy (n : ℕ) : ℝ := ((1 : ℝ) / 2) ^ n

theorem selectionAccuracy_pos (n : ℕ) : 0 < selectionAccuracy n := by
  simp [selectionAccuracy]

theorem summable_selectionAccuracy : Summable selectionAccuracy := by
  exact summable_geometric_of_lt_one (by norm_num) (by norm_num)

theorem tendsto_selectionAccuracy_zero :
    Tendsto selectionAccuracy atTop (𝓝 0) := by
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- Data maintained at stage `n` of the KRN construction.-/
structure EffrosSelectionStage
    {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    (S : Ω → Set E) (n : ℕ) where
  toFun : Ω → E
  measurable' : Measurable toFun
  denseValued' : IsDenseSeqValued toFun
  close' : ∀ ω, infDist (toFun ω) (S ω) < selectionAccuracy n

def initialEffrosSelectionStage
    {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hne : ∀ ω, (S ω).Nonempty) : EffrosSelectionStage S 0 where
  toFun := effrosApproximateSelection S hne (selectionAccuracy 0)
    (selectionAccuracy_pos 0)
  measurable' := measurable_effrosApproximateSelection hS hne
    (selectionAccuracy_pos 0)
  denseValued' := isDenseSeqValued_effrosApproximateSelection
    S hne (selectionAccuracy 0) (selectionAccuracy_pos 0)
  close' := infDist_effrosApproximateSelection_lt
    S hne (selectionAccuracy_pos 0)

def nextEffrosSelectionStage
    {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hne : ∀ ω, (S ω).Nonempty) {n : ℕ}
    (prev : EffrosSelectionStage S n) : EffrosSelectionStage S (n + 1) := by
  let G : Ω → Set E :=
    fun ω => S ω ∩ Metric.ball (prev.toFun ω) (selectionAccuracy n)
  have hG : RandomSet.IsEffrosMeasurable G :=
    RandomSet.IsEffrosMeasurable.inter_ball_of_isDenseSeqValued
      hS prev.measurable' prev.denseValued' (selectionAccuracy n)
  have hGne : ∀ ω, (G ω).Nonempty :=
    nonempty_inter_ball_of_infDist_lt hne prev.close'
  let next : Ω → E :=
    effrosApproximateSelection G hGne (selectionAccuracy (n + 1))
      (selectionAccuracy_pos (n + 1))
  refine
    { toFun := next
      measurable' := measurable_effrosApproximateSelection hG hGne
        (selectionAccuracy_pos (n + 1))
      denseValued' := isDenseSeqValued_effrosApproximateSelection
        G hGne (selectionAccuracy (n + 1)) (selectionAccuracy_pos (n + 1))
      close' := ?_ }
  intro ω
  have hnextG : infDist (next ω) (G ω) < selectionAccuracy (n + 1) :=
    infDist_effrosApproximateSelection_lt G hGne
      (selectionAccuracy_pos (n + 1)) ω
  obtain ⟨x, hxG, hnextx⟩ := (infDist_lt_iff (hGne ω)).mp hnextG
  exact (infDist_le_dist_of_mem hxG.1).trans_lt hnextx

theorem nextEffrosSelectionStage_dist_lt
    {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hne : ∀ ω, (S ω).Nonempty) {n : ℕ}
    (prev : EffrosSelectionStage S n) (ω : Ω) :
    dist ((nextEffrosSelectionStage (S := S) hS hne prev).toFun ω) (prev.toFun ω) <
      selectionAccuracy (n + 1) + selectionAccuracy n := by
  let G : Ω → Set E :=
    fun ω => S ω ∩ Metric.ball (prev.toFun ω) (selectionAccuracy n)
  have hGne : ∀ ω, (G ω).Nonempty :=
    nonempty_inter_ball_of_infDist_lt hne prev.close'
  have hnextG :
      infDist
        (effrosApproximateSelection G hGne (selectionAccuracy (n + 1))
          (selectionAccuracy_pos (n + 1)) ω)
        (G ω) < selectionAccuracy (n + 1) :=
    infDist_effrosApproximateSelection_lt G hGne
      (selectionAccuracy_pos (n + 1)) ω
  obtain ⟨x, hxG, hnextx⟩ := (infDist_lt_iff (hGne ω)).mp hnextG
  change dist
      (effrosApproximateSelection G hGne (selectionAccuracy (n + 1))
        (selectionAccuracy_pos (n + 1)) ω)
      (prev.toFun ω) < selectionAccuracy (n + 1) + selectionAccuracy n
  calc
    dist
        (effrosApproximateSelection G hGne (selectionAccuracy (n + 1))
          (selectionAccuracy_pos (n + 1)) ω)
        (prev.toFun ω) ≤
        dist
          (effrosApproximateSelection G hGne (selectionAccuracy (n + 1))
            (selectionAccuracy_pos (n + 1)) ω) x +
          dist x (prev.toFun ω) := dist_triangle _ _ _
    _ < selectionAccuracy (n + 1) + selectionAccuracy n := by
      apply add_lt_add hnextx
      simpa [G, Metric.mem_ball] using hxG.2

/-- The recursively constructed coherent approximate selections.-/
def krnStage
    {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hne : ∀ ω, (S ω).Nonempty) :
    (n : ℕ) → EffrosSelectionStage S n
  | 0 => initialEffrosSelectionStage hS hne
  | n + 1 => nextEffrosSelectionStage hS hne (krnStage hS hne n)

def krnApproximation
    {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hne : ∀ ω, (S ω).Nonempty) (n : ℕ) : Ω → E :=
  (krnStage hS hne n).toFun

theorem krnApproximation_measurable
    {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hne : ∀ ω, (S ω).Nonempty) (n : ℕ) :
    Measurable (krnApproximation hS hne n) :=
  (krnStage hS hne n).measurable'

theorem krnApproximation_close
    {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hne : ∀ ω, (S ω).Nonempty) (n : ℕ) (ω : Ω) :
    infDist (krnApproximation hS hne n ω) (S ω) < selectionAccuracy n :=
  (krnStage hS hne n).close' ω

theorem krnApproximation_dist_succ_lt
    {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hne : ∀ ω, (S ω).Nonempty) (n : ℕ) (ω : Ω) :
    dist (krnApproximation hS hne (n + 1) ω)
        (krnApproximation hS hne n ω) <
      selectionAccuracy (n + 1) + selectionAccuracy n := by
  exact nextEffrosSelectionStage_dist_lt hS hne (krnStage hS hne n) ω

theorem krnApproximation_cauchySeq
    {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hne : ∀ ω, (S ω).Nonempty) (ω : Ω) :
    CauchySeq (fun n => krnApproximation hS hne n ω) := by
  apply cauchySeq_of_dist_le_of_summable
    (fun n => selectionAccuracy (n + 1) + selectionAccuracy n)
  · intro n
    simpa [dist_comm] using (krnApproximation_dist_succ_lt hS hne n ω).le
  · have hsucc : Summable (fun n => selectionAccuracy (n + 1)) := by
      simpa [Function.comp_def] using
        summable_selectionAccuracy.comp_injective Nat.succ_injective
    exact hsucc.add summable_selectionAccuracy

/-- The pointwise limit of the coherent approximations.-/
def krnSelection
    {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hne : ∀ ω, (S ω).Nonempty) (ω : Ω) : E :=
  atTop.limUnder (fun n => krnApproximation hS hne n ω)

/-- **Kuratowski--Ryll-Nardzewski theorem**: a nonempty closed-valued
Effros-measurable correspondence into a complete separable metric space has a
measurable selection.-/
theorem kuratowski_ryll_nardzewski
    {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hclosed : ∀ ω, IsClosed (S ω)) (hne : ∀ ω, (S ω).Nonempty) :
    IsMeasurableSelection S (krnSelection hS hne) := by
  apply isMeasurableSelection_of_tendsto_infDist_zero hclosed hne
  · exact krnApproximation_measurable hS hne
  · intro ω
    exact (krnApproximation_cauchySeq hS hne ω).tendsto_limUnder
  · intro ω
    apply squeeze_zero
    · exact fun _ => infDist_nonneg
    · intro n
      exact (krnApproximation_close hS hne n ω).le
    · exact tendsto_selectionAccuracy_zero

theorem exists_measurableSelection
    {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    {S : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hclosed : ∀ ω, IsClosed (S ω)) (hne : ∀ ω, (S ω).Nonempty) :
    ∃ f : Ω → E, Measurable f ∧ ∀ ω, f ω ∈ S ω := by
  exact ⟨krnSelection hS hne, kuratowski_ryll_nardzewski hS hclosed hne⟩

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
