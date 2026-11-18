import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Complex_differentiableOn_integral_of_continuousOn_of_forall_differentiableOn

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Complex_differentiableOn_integral_of_continuousOn_of_forall_differentiableOn.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=differen.5h5v.s8.5ea2160876ca from=translated src=- shape=e4ce6b8a vocab=c4cda6e6
-/
theorem Complex.differentiableOn_integral_of_continuousOn_of_forall_differentiableOn
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (ν : MeasureTheory.Measure Y) [MeasureTheory.IsFiniteMeasureOnCompacts ν]
    {U : Set ℂ} (hU : IsOpen U) {S : Set Y} (hS : IsCompact S)
    (F : ℂ → Y → ℂ) (hF : ContinuousOn (Function.uncurry F) (U ×ˢ Set.univ))
    (hFS : ∀ z ∈ U, ∀ a ∉ S, F z a = 0)
    (hhol : ∀ a : Y, DifferentiableOn ℂ (fun z => F z a) U) :
    DifferentiableOn ℂ (fun z => ∫ a, F z a ∂ν) U := by exact @_root_.P2MW.S_Complex_differentiableOn_integral_of_continuousOn_of_forall_differentiableOn.solution Y _ _ _ ν _ U hU S hS F hF hFS hhol
