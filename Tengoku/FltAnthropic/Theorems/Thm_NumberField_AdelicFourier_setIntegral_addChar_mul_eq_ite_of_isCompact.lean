import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicFourier
import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicBox
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Tengoku.FltAnthropic.P2M.Sol.S_NumberField_AdelicFourier_setIntegral_addChar_mul_eq_ite_of_isCompact

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_NumberField_AdelicFourier_setIntegral_addChar_mul_eq_ite_of_isCompact.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors
theorem NumberField.AdelicFourier.setIntegral_addChar_mul_eq_ite_of_isCompact
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ)
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F)) (hK : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (ξ : FiniteAdeleRing (𝓞 F) F) :
    ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), ψf (ξ * z) ∂ν
      = if (∀ z ∈ K, ψf (ξ * z) = 1) then ((ν K).toReal : ℂ) else 0 := by exact @_root_.P2MW.S_NumberField_AdelicFourier_setIntegral_addChar_mul_eq_ite_of_isCompact.solution F _ _ _ _ ν _ ψf K hK ξ
