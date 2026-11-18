import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingModel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_UVCrossingModel_crossingSwap_U.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_UVCrossingModel_crossingSwap_U

open ModularCurve ModularCurve.UVCrossingModel

/--
@isnad1 id=eq.0h2v.s8.33db5f0236ff from=translated src=- shape=124d16d6 vocab=ef9ab85a
-/
theorem solution {W : Type*} [CommRing W] (π : W) :
    crossingSwap π (U π) = V π :=
  by
  have h : crossingSwap π (UVCrossingModel.mk π (MvPowerSeries.X 0)) =
      UVCrossingModel.mk π (uvSwapEquiv (MvPowerSeries.X 0)) := crossingSwap_mk π _
  rw [uvSwapEquiv_X_zero] at h
  exact h
