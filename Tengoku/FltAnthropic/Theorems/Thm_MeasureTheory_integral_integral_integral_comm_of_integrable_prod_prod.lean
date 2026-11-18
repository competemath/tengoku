import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MeasureTheory_integral_integral_integral_comm_of_integrable_prod_prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MeasureTheory_integral_integral_integral_comm_of_integrable_prod_prod.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory Set

/--
@isnad1 id=eq.1h8v.s7.073a80006fa3 from=translated src=- shape=bba93661 vocab=1b1c9397
-/
theorem MeasureTheory.integral_integral_integral_comm_of_integrable_prod_prod
    {X Y Z E : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure Y) (ρ : Measure Z) [SFinite μ] [SFinite ν] [SFinite ρ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : X × Y × Z → E) (hf : Integrable f (μ.prod (ν.prod ρ))) :
    ∫ x, ∫ y, ∫ z, f (x, y, z) ∂ρ ∂ν ∂μ = ∫ z, ∫ y, ∫ x, f (x, y, z) ∂μ ∂ν ∂ρ := by exact @_root_.P2MW.S_MeasureTheory_integral_integral_integral_comm_of_integrable_prod_prod.solution X Y Z E _ _ _ μ ν ρ _ _ _ _ _ _ f hf
