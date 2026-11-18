import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicHaar
import Tengoku.Seed.MeasureTheory.Measure.Haar.DistribChar
import Tengoku.FltAnthropic.P2M.Sol.S_NumberField_AdeleRing_distribHaarChar_algebraMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_NumberField_AdeleRing_distribHaarChar_algebraMap.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open NumberField
/--
@isnad1 id=eq.0h2v.s11.6f8253c2900f from=translated src=- shape=ad9cd3ee vocab=05e0d30e
-/
theorem NumberField.AdeleRing.distribHaarChar_algebraMap (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] (a : Fˣ) :
    MeasureTheory.distribHaarChar (AdeleRing (𝓞 F) F)
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a) = 1 := by exact @_root_.P2MW.S_NumberField_AdeleRing_distribHaarChar_algebraMap.solution F _ _ _ _ a
