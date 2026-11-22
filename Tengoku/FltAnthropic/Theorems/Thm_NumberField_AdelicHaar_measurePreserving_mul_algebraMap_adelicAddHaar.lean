import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicBox
import Tengoku.FltAnthropic.P2M.Sol.S_NumberField_AdelicHaar_measurePreserving_mul_algebraMap_adelicAddHaar

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_NumberField_AdelicHaar_measurePreserving_mul_algebraMap_adelicAddHaar.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open NumberField
attribute [local instance] NumberField.AdelicHaar.adeleBorel
/--
@isnad1 id=measurep.1h2v.s9.b29f7ea99808 from=translated src=- shape=0049ab5a vocab=937ef54f
-/
theorem NumberField.AdelicHaar.measurePreserving_mul_algebraMap_adelicAddHaar
    (F : Type) [Field F] [NumberField F] (a : F) (ha : a ≠ 0) :
    MeasureTheory.MeasurePreserving (fun x => algebraMap F (AdeleRing (𝓞 F) F) a * x)
      (AdelicHaar.adelicAddHaar (𝓞 F) F) (AdelicHaar.adelicAddHaar (𝓞 F) F) := by exact @_root_.P2MW.S_NumberField_AdelicHaar_measurePreserving_mul_algebraMap_adelicAddHaar.solution F _ _ a ha
