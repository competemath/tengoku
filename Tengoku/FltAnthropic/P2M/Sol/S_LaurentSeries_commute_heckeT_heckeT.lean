import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_LaurentSeries_HeckeU
import Tengoku.FltAnthropic.Definitions.Def_LaurentSeries_HeckeV
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff
import Tengoku.FltAnthropic.Theorems.Thm_LaurentSeries_commute_heckeU_heckeU
import Tengoku.FltAnthropic.Theorems.Thm_LaurentSeries_commute_heckeU_heckeV
import Tengoku.FltAnthropic.Theorems.Thm_LaurentSeries_commute_heckeV_heckeV

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LaurentSeries_commute_heckeT_heckeT.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LaurentSeries_commute_heckeT_heckeT

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

set_option autoImplicit false

open ModularCurve LaurentSeries

theorem solution (R : Type*) [CommRing R] (ℓ ℓ' : ℕ) (hℓ : 0 < ℓ) (hℓ' : 0 < ℓ') (k : ℕ)
    (h : Nat.Coprime ℓ ℓ') :
    Commute (heckeT R ℓ hℓ k) (heckeT R ℓ' hℓ' k)  := by
  have h1 := commute_heckeU_heckeU R ℓ ℓ' hℓ hℓ'
  have h2 := commute_heckeU_heckeV R ℓ ℓ' hℓ hℓ' h
  have h3 := (commute_heckeU_heckeV R ℓ' ℓ hℓ' hℓ h.symm).symm
  have h4 := commute_heckeV_heckeV R ℓ ℓ' hℓ hℓ' h
  exact (h1.add_right (h2.smul_right _)).add_left ((h3.add_right (h4.smul_right _)).smul_left _)
