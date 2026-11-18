import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicBox
import Tengoku.FltAnthropic.P2M.Sol.S_NumberField_AdelicBox_isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_NumberField_AdelicBox_isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open NumberField
/--
@isnad1 id=isaddfun.1h3v.s11.e1cdf35a34c6 from=translated src=- shape=27364ffc vocab=e36f7c4c
-/
theorem NumberField.AdelicBox.isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) (a : F) (ha : a ≠ 0) :
    MeasureTheory.IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F)
      ((fun x => algebraMap F (AdeleRing (𝓞 F) F) a * x) ⁻¹' AdelicBox.adelicBox F) μ := by exact @_root_.P2MW.S_NumberField_AdelicBox_isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox.solution F _ _ _ _ μ a ha
