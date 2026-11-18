import Tengoku.Seed.Analysis.MellinTransform
import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_ArchBessel
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_ArchBessel_hasDerivAt_besselKernel_and_hasDerivAt_deriv_besselKernel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_ArchBessel_hasDerivAt_besselKernel_and_hasDerivAt_deriv_besselKernel.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open _root_.LanglandsTunnell.ArchBessel hiding hasDerivAt_besselKernel mul_besselKernel_eq_mul_sub

/--
@isnad1 id=and.1h2v.s8.80b4cc75bf99 from=translated src=- shape=eb94c7c0 vocab=ce1ae00d
-/
theorem LanglandsTunnell.ArchBessel.hasDerivAt_besselKernel_and_hasDerivAt_deriv_besselKernel
    (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => besselKernel ν x) (-besselKernel (ν + 1) x + ν / (x : ℂ) * besselKernel ν x) x ∧
      HasDerivAt (deriv fun x : ℝ => besselKernel ν x)
        ((1 + ν ^ 2 / (x : ℂ) ^ 2) * besselKernel ν x - (deriv (fun x : ℝ => besselKernel ν x) x) / (x : ℂ)) x := by exact @_root_.P2MW.S_LanglandsTunnell_ArchBessel_hasDerivAt_besselKernel_and_hasDerivAt_deriv_besselKernel.solution ν x hx
