import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicFourier
import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicBox
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Tengoku.FltAnthropic.P2M.Sol.S_NumberField_AdelicFourier_fourierIntegral_indicator_principalCoset_finiteAdeleRing_apply

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_NumberField_AdelicFourier_fourierIntegral_indicator_principalCoset_finiteAdeleRing_apply.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors
open scoped Classical in
theorem NumberField.AdelicFourier.fourierIntegral_indicator_principalCoset_finiteAdeleRing_apply
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    {ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ} (hψf : Continuous ψf)
    (d : 𝓞 F) (hd : d ≠ 0) (k : F) (w : FiniteAdeleRing (𝓞 F) F) :
    fourierIntegral ψf ν
        (((fun z ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
            integralFiniteAdeles (𝓞 F) F).indicator 1)
        w
      = ψf (-(algebraMap F (FiniteAdeleRing (𝓞 F) F) k * w))
        * ((ν ((fun z ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
            integralFiniteAdeles (𝓞 F) F)).toReal : ℂ)
        * (if ∀ z ∈ integralFiniteAdeles (𝓞 F) F,
              ψf (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * w * z) = 1
            then 1 else 0) := by exact @_root_.P2MW.S_NumberField_AdelicFourier_fourierIntegral_indicator_principalCoset_finiteAdeleRing_apply.solution F _ _ _ _ ν _ ψf hψf d hd k w
