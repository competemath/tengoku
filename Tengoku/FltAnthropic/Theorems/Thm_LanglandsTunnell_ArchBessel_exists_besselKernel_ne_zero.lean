import Tengoku.Seed.Analysis.MellinTransform
import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_ArchBessel
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_ArchBessel_exists_besselKernel_ne_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_ArchBessel_exists_besselKernel_ne_zero.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open _root_.LanglandsTunnell.ArchBessel hiding mellin_besselKernel_eq_mul_Gamma_mul_Gamma

/--
@isnad1 id=ex.0h1v.s4.ebcc777ce111 from=translated src=- shape=447ca309 vocab=e6433e7c
-/
theorem LanglandsTunnell.ArchBessel.exists_besselKernel_ne_zero (ν : ℂ) :
    ∃ x : ℝ, 0 < x ∧ besselKernel ν x ≠ 0 := by exact @_root_.P2MW.S_LanglandsTunnell_ArchBessel_exists_besselKernel_ne_zero.solution ν
