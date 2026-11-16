import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_PadicAlgCl_isIntegral_padicInt_iff_norm_le_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_PadicAlgCl_isIntegral_padicInt_iff_norm_le_one.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=iff.0h2v.s6.2b1fcc7ba260 from=translated src=- shape=073b9a6c vocab=dc025562
-/
theorem PadicAlgCl.isIntegral_padicInt_iff_norm_le_one (p : ℕ) [Fact p.Prime]
    (x : PadicAlgCl p) : IsIntegral ℤ_[p] x ↔ ‖x‖ ≤ 1 := by exact @_root_.P2MW.S_PadicAlgCl_isIntegral_padicInt_iff_norm_le_one.solution p _ x
