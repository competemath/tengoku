import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_mem_laurentBaseChange_iff_exists_eq_sum_smul_coeffEmb

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_mem_laurentBaseChange_iff_exists_eq_sum_smul_coeffEmb.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped BigOperators

theorem ModularCurve.mem_laurentBaseChange_iff_exists_eq_sum_smul_coeffEmb
    (L : Type) [Field L] [CharZero L]
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℚ L)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (f : LaurentSeries L) :
    f ∈ ModularCurve.laurentBaseChange L F₀ ↔
      ∃ h : ι → ↥F₀, f = ∑ i, (b i) • ModularCurve.coeffEmb L ((h i : ↥F₀) : LaurentSeries ℚ) := by exact @_root_.P2MW.S_ModularCurve_mem_laurentBaseChange_iff_exists_eq_sum_smul_coeffEmb.solution L _ _ ι _ b F₀ f
