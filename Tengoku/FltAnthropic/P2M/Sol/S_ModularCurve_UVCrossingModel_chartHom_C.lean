import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingChart

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_UVCrossingModel_chartHom_C.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_UVCrossingModel_chartHom_C

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] (π : W) (w : W) :
    chartHom π (PowerSeries.C w) = const π w :=
  by
  rw [chartHom_apply, PowerSeries.subst_C]
  rfl
