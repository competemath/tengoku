import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_CompletionBridge
import Tengoku.FltAnthropic.P2M.Sol.S_localGaloisToGlobal_mem_fixingSubgroup_iff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_localGaloisToGlobal_mem_fixingSubgroup_iff.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false
open scoped IntermediateField
/--
@isnad1 id=iff.0h3v.s12.c7b14d67991e from=translated src=- shape=6c83ae1f vocab=4bac702a
-/
theorem _root_.Tengoku.FltAnthropic.localGaloisToGlobal_mem_fixingSubgroup_iff
    (q : ℕ) [Fact q.Prime]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (s : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) :
    localGaloisToGlobal q s ∈ F.fixingSubgroup ↔
      s ∈ (IntermediateField.adjoin ℚ_[q]
        (padicEmbedding q '' (F : Set (AlgebraicClosure ℚ)))).fixingSubgroup := by exact @_root_.P2MW.S_localGaloisToGlobal_mem_fixingSubgroup_iff.solution q _ F s
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
