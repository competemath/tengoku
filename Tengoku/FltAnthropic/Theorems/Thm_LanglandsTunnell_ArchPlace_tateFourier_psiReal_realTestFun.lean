import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_TateLocalZeta
import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_ArchPlace
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_ArchPlace_tateFourier_psiReal_realTestFun

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_ArchPlace_tateFourier_psiReal_realTestFun.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
attribute [-simp] LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq

set_option autoImplicit false

open MeasureTheory LanglandsTunnell LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace

/--
@isnad1 id=eq.0h2v.s5.5bc77c218bea from=translated src=- shape=f78acf6a vocab=d2747fcc
-/
theorem LanglandsTunnell.ArchPlace.tateFourier_psiReal_realTestFun (a : ZMod 2) (y : ℝ) :
    tateFourier psiReal volume (realTestFun a) y = (-Complex.I) ^ a.val * realTestFun a y := by exact @_root_.P2MW.S_LanglandsTunnell_ArchPlace_tateFourier_psiReal_realTestFun.solution a y
