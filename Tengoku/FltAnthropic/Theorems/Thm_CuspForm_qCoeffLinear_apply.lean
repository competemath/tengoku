import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CuspForm_QCoeffLinear
import Tengoku.FltAnthropic.P2M.Sol.S_CuspForm_qCoeffLinear_apply

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CuspForm_qCoeffLinear_apply.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem CuspForm.qCoeffLinear_apply (M : ℕ) (k : ℤ) (n : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 M) k) :
    CuspForm.qCoeffLinear M k n f = ModularFormClass.qCoeff (⇑f) n := by exact @_root_.P2MW.S_CuspForm_qCoeffLinear_apply.solution M k n f
