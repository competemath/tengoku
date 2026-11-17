import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_CompletionBridge
import Tengoku.FltAnthropic.Definitions.Def_ExtCitation_KummerBridge
import Tengoku.FltAnthropic.P2M.Sol.S_ExtCitation_exists_isPrimitiveRoot_smul_eq_pow_cycloChar_localGaloisToGlobal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ExtCitation_exists_isPrimitiveRoot_smul_eq_pow_cycloChar_localGaloisToGlobal.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false
open ExtCitation
theorem ExtCitation.exists_isPrimitiveRoot_smul_eq_pow_cycloChar_localGaloisToGlobal
    (q : ℕ) [Fact q.Prime] (p : ℕ) [Fact p.Prime] :
    ∃ ζ : (PadicAlgCl q)ˣ, IsPrimitiveRoot ζ p ∧ ∀ g : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q,
      g • ζ = ζ ^ (cycloChar p (localGaloisToGlobal q g) : ZMod p).val := by exact @_root_.P2MW.S_ExtCitation_exists_isPrimitiveRoot_smul_eq_pow_cycloChar_localGaloisToGlobal.solution q _ p _
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
