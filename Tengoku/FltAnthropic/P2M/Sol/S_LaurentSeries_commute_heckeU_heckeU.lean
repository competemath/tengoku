import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_LaurentSeries_HeckeU
import Tengoku.FltAnthropic.Definitions.Def_LaurentSeries_HeckeV
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LaurentSeries_commute_heckeU_heckeU.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LaurentSeries_commute_heckeU_heckeU

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

set_option autoImplicit false

open ModularCurve LaurentSeries

theorem solution (R : Type*) [CommRing R] (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Commute (heckeU R a ha) (heckeU R b hb)  := by
  ext f n
  simp only [Module.End.mul_apply, coeff_heckeU]
  ring_nf
