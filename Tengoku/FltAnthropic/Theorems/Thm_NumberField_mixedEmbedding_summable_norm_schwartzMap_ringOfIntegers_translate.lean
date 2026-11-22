import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicFourier
import Tengoku.Seed.Algebra.Module.ZLattice.Summable
import Tengoku.FltAnthropic.P2M.Sol.S_NumberField_mixedEmbedding_summable_norm_schwartzMap_ringOfIntegers_translate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_NumberField_mixedEmbedding_summable_norm_schwartzMap_ringOfIntegers_translate.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open NumberField NumberField.mixedEmbedding
open scoped SchwartzMap Classical

noncomputable section
/--
@isnad1 id=summable.0h3v.s11.318c15f943d2 from=translated src=- shape=ca620796 vocab=27ec9667
-/
theorem NumberField.mixedEmbedding.summable_norm_schwartzMap_ringOfIntegers_translate
    (F : Type*) [Field F] [NumberField F]
    (g : 𝓢(NumberField.mixedEmbedding.mixedSpace F, ℂ))
    (x : NumberField.mixedEmbedding.mixedSpace F) :
    Summable fun a : 𝓞 F => ‖g (x + NumberField.mixedEmbedding F (a : F))‖ := by exact @_root_.P2MW.S_NumberField_mixedEmbedding_summable_norm_schwartzMap_ringOfIntegers_translate.solution F _ _ g x
