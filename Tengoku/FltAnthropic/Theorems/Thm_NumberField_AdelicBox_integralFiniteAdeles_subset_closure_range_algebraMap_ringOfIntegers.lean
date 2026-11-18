import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicBox
import Tengoku.FltAnthropic.P2M.Sol.S_NumberField_AdelicBox_integralFiniteAdeles_subset_closure_range_algebraMap_ringOfIntegers

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_NumberField_AdelicBox_integralFiniteAdeles_subset_closure_range_algebraMap_ringOfIntegers.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open NumberField NumberField.AdelicBox IsDedekindDomain
open scoped Classical nonZeroDivisors
theorem NumberField.AdelicBox.integralFiniteAdeles_subset_closure_range_algebraMap_ringOfIntegers
    (F : Type) [Field F] [NumberField F] :
    integralFiniteAdeles (𝓞 F) F
      ⊆ closure (Set.range (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F))) := by exact @_root_.P2MW.S_NumberField_AdelicBox_integralFiniteAdeles_subset_closure_range_algebraMap_ringOfIntegers.solution F _ _
