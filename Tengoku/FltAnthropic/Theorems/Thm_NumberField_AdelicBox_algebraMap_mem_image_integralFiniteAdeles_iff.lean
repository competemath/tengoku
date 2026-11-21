import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicBox
import Tengoku.FltAnthropic.P2M.Sol.S_NumberField_AdelicBox_algebraMap_mem_image_integralFiniteAdeles_iff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_NumberField_AdelicBox_algebraMap_mem_image_integralFiniteAdeles_iff.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open NumberField NumberField.AdelicBox IsDedekindDomain
open scoped nonZeroDivisors
/--
@isnad1 id=iff.1h4v.s10.cfff958cd5a5 from=translated src=- shape=d98557ff vocab=801045c6
-/
theorem NumberField.AdelicBox.algebraMap_mem_image_integralFiniteAdeles_iff
    (F : Type) [Field F] [NumberField F] (d : 𝓞 F) (hd : d ≠ 0) (k ξ : F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ ∈
        (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F
      ↔ ∃ a : 𝓞 F, ξ = k + (d : F) * (a : F) := by exact @_root_.P2MW.S_NumberField_AdelicBox_algebraMap_mem_image_integralFiniteAdeles_iff.solution F _ _ d hd k ξ
