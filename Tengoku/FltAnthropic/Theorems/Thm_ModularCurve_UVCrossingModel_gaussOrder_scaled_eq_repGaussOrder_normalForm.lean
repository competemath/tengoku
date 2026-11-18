import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingModel
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingDominantIndices
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_UVCrossingModel_gaussOrder_scaled_eq_repGaussOrder_normalForm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_UVCrossingModel_gaussOrder_scaled_eq_repGaussOrder_normalForm.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

theorem ModularCurve.UVCrossingModel.gaussOrder_scaled_eq_repGaussOrder_normalForm
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (q : ℕ) (hq : 1 ≤ q)
    (x : UVCrossingModel W (ϖ ^ e))
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x) (p : ℕ) (hp : p ≤ q * e) :
    gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) p x = repGaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p (inU ab.1 + inV ab.2) := by exact @_root_.P2MW.S_ModularCurve_UVCrossingModel_gaussOrder_scaled_eq_repGaussOrder_normalForm.solution W _ _ _ _ ϖ hϖ e he q hq x ab hb habx p hp
