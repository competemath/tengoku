import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingModel
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingDominantIndices
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_UVCrossingModel_repGaussOrder_normalForm_eq_iInf_termOrder

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_UVCrossingModel_repGaussOrder_normalForm_eq_iInf_termOrder.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

/--
@isnad1 id=eq.2h5v.s7.65f409116680 from=translated src=- shape=1daa7f33 vocab=bee27d1a
-/
theorem ModularCurve.UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder
    {W : Type u} [CommRing W] (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) :
    repGaussOrder v E t (inU ab.1 + inV ab.2) = ⨅ n : ℤ, termOrder v E t ab n := by exact @_root_.P2MW.S_ModularCurve_UVCrossingModel_repGaussOrder_normalForm_eq_iInf_termOrder.solution W _ v hv0 E t ab hb
