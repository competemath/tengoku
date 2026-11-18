import Tengoku.Seed.Analysis.MellinTransform
import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_ArchBessel
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_ArchBessel_integrableOn_exp_neg_mul_add_inv_mul_cpow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_ArchBessel_integrableOn_exp_neg_mul_add_inv_mul_cpow.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open LanglandsTunnell.ArchBessel

theorem LanglandsTunnell.ArchBessel.integrableOn_exp_neg_mul_add_inv_mul_cpow (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => (Real.exp (-(x * (t + t⁻¹) / 2)) : ℂ) * ((t : ℂ) ^ (ν - 1))) (Set.Ioi 0) := by exact @_root_.P2MW.S_LanglandsTunnell_ArchBessel_integrableOn_exp_neg_mul_add_inv_mul_cpow.solution ν x hx
