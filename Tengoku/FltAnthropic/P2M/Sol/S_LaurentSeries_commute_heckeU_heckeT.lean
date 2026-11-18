import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_LaurentSeries_HeckeU
import Tengoku.FltAnthropic.Definitions.Def_LaurentSeries_HeckeV
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff
import Tengoku.FltAnthropic.Theorems.Thm_LaurentSeries_commute_heckeU_heckeU
import Tengoku.FltAnthropic.Theorems.Thm_LaurentSeries_commute_heckeU_heckeV

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LaurentSeries_commute_heckeU_heckeT.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LaurentSeries_commute_heckeU_heckeT

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

set_option autoImplicit false

open ModularCurve LaurentSeries

/--
@isnad1 id=commute.3h4v.s7.7a731eb2982c from=translated src=- shape=c1c25bee vocab=478cf0da
-/
theorem solution (R : Type*) [CommRing R] (p ℓ : ℕ) (hp : 0 < p) (hℓ : 0 < ℓ) (k : ℕ)
    (hpl : Nat.Coprime p ℓ) :
    Commute (heckeU R p hp) (heckeT R ℓ hℓ k)  :=
  (commute_heckeU_heckeU R p ℓ hp hℓ).add_right ((commute_heckeU_heckeV R p ℓ hp hℓ hpl).smul_right _)
