import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MeasureTheory_measure_setOf_exists_mem_le_mul_of_forall_closedBall

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MeasureTheory_measure_setOf_exists_mem_le_mul_of_forall_closedBall.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem MeasureTheory.measure_setOf_exists_mem_le_mul_of_forall_closedBall
    {α β : Type*} [MetricSpace α] [SecondCountableTopology α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [HasBesicovitchCovering α] {_ : MeasurableSpace β} (μ : Measure β) (ν : Measure α) [SFinite ν]
    [ν.OuterRegular] (P : β → α → Prop) (S : Set α) (K : ℝ≥0∞) (hK : K ≠ ⊤)
    (h : ∀ x ∈ S, ∃ δ > 0, ∀ ρ ∈ Set.Ioo 0 δ,
      μ {b | ∃ y ∈ Metric.closedBall x ρ, P b y} ≤ K * ν (Metric.closedBall x ρ)) :
    μ {b | ∃ x ∈ S, P b x} ≤ K * ν S := by exact @_root_.P2MW.S_MeasureTheory_measure_setOf_exists_mem_le_mul_of_forall_closedBall.solution α β _ _ _ _ _ ‹MeasurableSpace β› μ ν _ _ P S K hK h
