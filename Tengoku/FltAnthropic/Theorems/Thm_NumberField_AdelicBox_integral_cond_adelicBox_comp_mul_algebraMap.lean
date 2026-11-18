import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicBox
import Tengoku.FltAnthropic.P2M.Sol.S_NumberField_AdelicBox_integral_cond_adelicBox_comp_mul_algebraMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_NumberField_AdelicBox_integral_cond_adelicBox_comp_mul_algebraMap.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open NumberField
attribute [local instance] NumberField.AdelicHaar.adeleBorel
theorem NumberField.AdelicBox.integral_cond_adelicBox_comp_mul_algebraMap
    (F : Type) [Field F] [NumberField F]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : AdeleRing (𝓞 F) F → E}
    (hf : ∀ (k : F) (x : AdeleRing (𝓞 F) F), f (algebraMap F (AdeleRing (𝓞 F) F) k + x) = f x)
    (a : F) (ha : a ≠ 0) :
    ∫ x, f (algebraMap F (AdeleRing (𝓞 F) F) a * x)
        ∂(ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F))
      = ∫ x, f x ∂(ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) := by exact @_root_.P2MW.S_NumberField_AdelicBox_integral_cond_adelicBox_comp_mul_algebraMap.solution F _ _ E _ _ f hf a ha
