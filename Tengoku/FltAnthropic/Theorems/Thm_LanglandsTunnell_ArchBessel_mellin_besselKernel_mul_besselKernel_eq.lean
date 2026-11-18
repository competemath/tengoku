import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_ArchBessel
import Tengoku.Seed.Analysis.MellinTransform
import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Deligne
import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_ArchBessel_mellin_besselKernel_mul_besselKernel_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_ArchBessel_mellin_besselKernel_mul_besselKernel_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open Complex MeasureTheory Set LanglandsTunnell.ArchBessel

/--
@isnad1 id=and.1h3v.s8.70ea281a8e06 from=translated src=- shape=0cbf8077 vocab=a187a143
-/
theorem LanglandsTunnell.ArchBessel.mellin_besselKernel_mul_besselKernel_eq (μ ν s : ℂ) (hs : |μ.re| + |ν.re| < s.re) :
    MellinConvergent (fun x : ℝ => besselKernel μ x * besselKernel ν x) s ∧
      mellin (fun x : ℝ => besselKernel μ x * besselKernel ν x) s =
        (2 : ℂ) ^ (s - 1) *
          (Complex.Gamma ((s + μ + ν) / 2) * Complex.Gamma ((s + μ - ν) / 2) *
            Complex.Gamma ((s - μ + ν) / 2) * Complex.Gamma ((s - μ - ν) / 2)) / Complex.Gamma s := by exact @_root_.P2MW.S_LanglandsTunnell_ArchBessel_mellin_besselKernel_mul_besselKernel_eq.solution μ ν s hs
