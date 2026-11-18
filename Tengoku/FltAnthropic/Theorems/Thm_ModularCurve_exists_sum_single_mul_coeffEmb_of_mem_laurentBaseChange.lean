import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_exists_sum_single_mul_coeffEmb_of_mem_laurentBaseChange

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_exists_sum_single_mul_coeffEmb_of_mem_laurentBaseChange.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem ModularCurve.exists_sum_single_mul_coeffEmb_of_mem_laurentBaseChange
    (L : Type) [Field L] [CharZero L] [FiniteDimensional ℚ L]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (y : LaurentSeries L) (hy : y ∈ ModularCurve.laurentBaseChange L F₀) :
    ∃ (n : ℕ) (c : Fin n → L) (f : Fin n → LaurentSeries ℚ), (∀ i, f i ∈ F₀) ∧
      y = ∑ i, HahnSeries.single 0 (c i) * ModularCurve.coeffEmb L (f i) := by exact @_root_.P2MW.S_ModularCurve_exists_sum_single_mul_coeffEmb_of_mem_laurentBaseChange.solution L _ _ _ F₀ y hy
