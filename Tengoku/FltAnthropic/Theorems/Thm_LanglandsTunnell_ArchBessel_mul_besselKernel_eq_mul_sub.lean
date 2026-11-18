import Tengoku.Seed.Analysis.MellinTransform
import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_ArchBessel
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_ArchBessel_mul_besselKernel_eq_mul_sub

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_ArchBessel_mul_besselKernel_eq_mul_sub.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open _root_.LanglandsTunnell.ArchBessel hiding integrableOn_exp_neg_mul_add_inv_mul_cpow

theorem LanglandsTunnell.ArchBessel.mul_besselKernel_eq_mul_sub (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    ν * besselKernel ν x = (x : ℂ) / 2 * (besselKernel (ν + 1) x - besselKernel (ν - 1) x) := by exact @_root_.P2MW.S_LanglandsTunnell_ArchBessel_mul_besselKernel_eq_mul_sub.solution ν x hx
