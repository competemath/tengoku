import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff
import Tengoku.Seed.Algebra.Algebra.Subalgebra.Lattice
import Tengoku.Seed.LinearAlgebra.Finsupp.LinearCombination
import Tengoku.Seed.LinearAlgebra.Dual.Lemmas
import Tengoku.Seed.Data.Complex.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_mem_of_coeffEmb_mem_laurentBaseChange

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_mem_of_coeffEmb_mem_laurentBaseChange.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem ModularCurve.mem_of_coeffEmb_mem_laurentBaseChange (L : Type*) [Field L] [Algebra ℚ L]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (x : LaurentSeries ℚ)
    (hx : ModularCurve.coeffEmb L x ∈ ModularCurve.laurentBaseChange L F₀) : x ∈ F₀ := by exact @_root_.P2MW.S_ModularCurve_mem_of_coeffEmb_mem_laurentBaseChange.solution L _ _ F₀ x hx
