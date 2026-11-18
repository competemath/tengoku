import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_LaurentSeries_HeckeU
import Tengoku.FltAnthropic.Definitions.Def_LaurentSeries_HeckeV
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff
import Tengoku.FltAnthropic.P2M.Sol.S_LaurentSeries_commute_heckeV_heckeV

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LaurentSeries_commute_heckeV_heckeV.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open ModularCurve LaurentSeries

/--
@isnad1 id=commute.3h3v.s7.d8c1aad38c7a from=translated src=- shape=10d393b7 vocab=64292b42
-/
theorem LaurentSeries.commute_heckeV_heckeV (R : Type*) [CommRing R] (ℓ ℓ' : ℕ) (hℓ : 0 < ℓ) (hℓ' : 0 < ℓ')
    (h : Nat.Coprime ℓ ℓ') :
    Commute (heckeV R ℓ hℓ) (heckeV R ℓ' hℓ') := by exact @_root_.P2MW.S_LaurentSeries_commute_heckeV_heckeV.solution R _ ℓ ℓ' hℓ hℓ' h
