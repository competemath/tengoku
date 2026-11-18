import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingModel
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingDominantIndices
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_UVCrossingModel_dominantIndices_scale

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_UVCrossingModel_dominantIndices_scale.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

/--
@isnad1 id=eq.1h6v.s6.9b97c2358bd7 from=translated src=- shape=f9830ce7 vocab=5c93494d
-/
theorem ModularCurve.UVCrossingModel.dominantIndices_scale
    {W : Type u} [CommRing W] (v : W → ℕ∞) (E t q : ℕ) (hq : 1 ≤ q) (ab : PowerSeries W × PowerSeries W) :
    dominantIndices (fun w => (q : ℕ∞) * v w) (q * E) (q * t) ab = dominantIndices v E t ab := by exact @_root_.P2MW.S_ModularCurve_UVCrossingModel_dominantIndices_scale.solution W _ v E t q hq ab
