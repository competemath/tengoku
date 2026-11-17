import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_CompletionBridge
import Tengoku.FltAnthropic.P2M.Sol.S_IntermediateField_finiteDimensional_adjoin_padicEmbedding_image

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IntermediateField_finiteDimensional_adjoin_padicEmbedding_image.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false
open scoped IntermediateField
/--
@isnad1 id=finitedi.0h2v.s11.b6140a9a4402 from=translated src=- shape=0f4379ab vocab=d1e7ac10
-/
theorem IntermediateField.finiteDimensional_adjoin_padicEmbedding_image
    (q : ℕ) [Fact q.Prime]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] :
    FiniteDimensional ℚ_[q]
      (IntermediateField.adjoin ℚ_[q] (padicEmbedding q '' (F : Set (AlgebraicClosure ℚ)))) := by exact @_root_.P2MW.S_IntermediateField_finiteDimensional_adjoin_padicEmbedding_image.solution q _ F _
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
