import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MeasureTheory_differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MeasureTheory_differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory

/--
@isnad1 id=differen.4h4v.s8.0364d6f061ad from=translated src=- shape=81b3fa59 vocab=6bde5231
-/
theorem MeasureTheory.differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    {U : Set ℂ} (hU : IsOpen U) (F : ℂ → Y → ℂ)
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (F z) ν)
    (hhol : ∀ a : Y, DifferentiableOn ℂ (fun z => F z a) U)
    (hdom : ∀ z₀ ∈ U, ∃ ε : ℝ, 0 < ε ∧ ∃ M : Y → ℝ, Integrable M ν ∧
      ∀ z ∈ Metric.ball z₀ ε, ∀ a : Y, ‖F z a‖ ≤ M a) :
    DifferentiableOn ℂ (fun z => ∫ a, F z a ∂ν) U := by exact @_root_.P2MW.S_MeasureTheory_differentiableOn_integral_of_forall_differentiableOn_of_locally_norm_le.solution Y _ ν U hU F hmeas hhol hdom
