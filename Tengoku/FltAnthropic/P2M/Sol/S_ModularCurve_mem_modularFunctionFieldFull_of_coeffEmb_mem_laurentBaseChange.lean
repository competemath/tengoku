import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff
import Tengoku.FltAnthropic.Theorems.Thm_ModularCurve_mem_of_coeffEmb_mem_laurentBaseChange
import Tengoku.Seed.Data.Complex.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_mem_modularFunctionFieldFull_of_coeffEmb_mem_laurentBaseChange.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_mem_modularFunctionFieldFull_of_coeffEmb_mem_laurentBaseChange

theorem solution (N : ℕ) [NeZero N]
    (x : LaurentSeries ℚ)
    (hx : ModularCurve.coeffEmb ℂ x ∈
      ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) :
    x ∈ ModularCurve.modularFunctionFieldFull N :=
  ModularCurve.mem_of_coeffEmb_mem_laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N) x hx
