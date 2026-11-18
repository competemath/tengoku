import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_LaurentSeries_HeckeU
import Tengoku.FltAnthropic.Definitions.Def_LaurentSeries_HeckeV
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff
import Tengoku.FltAnthropic.P2M.Sol.S_LaurentSeries_commute_heckeU_heckeV

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LaurentSeries_commute_heckeU_heckeV.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open ModularCurve LaurentSeries

theorem LaurentSeries.commute_heckeU_heckeV (R : Type*) [CommRing R] (p ℓ : ℕ) (hp : 0 < p) (hℓ : 0 < ℓ)
    (hpl : Nat.Coprime p ℓ) :
    Commute (heckeU R p hp) (heckeV R ℓ hℓ) := by exact @_root_.P2MW.S_LaurentSeries_commute_heckeU_heckeV.solution R _ p ℓ hp hℓ hpl
