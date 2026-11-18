import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingModel
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingDominantIndices
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_UVCrossingModel_gaussOrder_sub_pred_eq_sSup_dominantIndices

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_UVCrossingModel_gaussOrder_sub_pred_eq_sSup_dominantIndices.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

/--
@isnad1 id=eq.9h7v.s10.84b803111a7f from=translated src=- shape=69a408e0 vocab=1f9c615d
-/
theorem ModularCurve.UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (q : ℕ) (hq : 1 ≤ q)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x) (p : ℕ) (hp1 : 1 ≤ p) (hpe : p ≤ q * e)
    (hleft : sSup (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab) ∈ dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) (p - 1) ab) :
    ((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) p x).toNat : ℤ) - (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (p - 1) x).toNat = sSup (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab) := by exact @_root_.P2MW.S_ModularCurve_UVCrossingModel_gaussOrder_sub_pred_eq_sSup_dominantIndices.solution W _ _ _ _ ϖ hϖ e he q hq x hx ab hb habx p hp1 hpe hleft
