import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Flat
import Tengoku.FltAnthropic.P2M.Sol.S_GaloisRep_mem_ratLocalizedAt_iff_padic_norm_le_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_GaloisRep_mem_ratLocalizedAt_iff_padic_norm_le_one.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=iff.0h2v.s6.b92bd7dd2719 from=translated src=- shape=d01bcb8c vocab=37501ad8
-/
theorem GaloisRep.mem_ratLocalizedAt_iff_padic_norm_le_one
    (p : ℕ) [Fact p.Prime] (q : ℚ) :
    q ∈ GaloisRep.ratLocalizedAt p ↔ ‖(q : ℚ_[p])‖ ≤ 1 := by exact @_root_.P2MW.S_GaloisRep_mem_ratLocalizedAt_iff_padic_norm_le_one.solution p _ q
