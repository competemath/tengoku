import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_CompletionBridge
import Tengoku.FltAnthropic.P2M.Sol.S_PadicAlgCl_exists_mem_adjoin_padicEmbedding

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_PadicAlgCl_exists_mem_adjoin_padicEmbedding.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false
open scoped IntermediateField
/--
@isnad1 id=ex.0h2v.s8.43de96a3784e from=translated src=- shape=812d27b2 vocab=e45e4e22
-/
theorem PadicAlgCl.exists_mem_adjoin_padicEmbedding
    (q : ℕ) [Fact q.Prime] (α : PadicAlgCl q) :
    ∃ b : AlgebraicClosure ℚ, α ∈ ℚ_[q]⟮padicEmbedding q b⟯ := by exact @_root_.P2MW.S_PadicAlgCl_exists_mem_adjoin_padicEmbedding.solution q _ α
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
