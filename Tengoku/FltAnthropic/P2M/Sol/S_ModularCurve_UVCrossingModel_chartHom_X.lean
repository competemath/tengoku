import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingChart

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_UVCrossingModel_chartHom_X.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_UVCrossingModel_chartHom_X

open ModularCurve ModularCurve.UVCrossingModel in
/--
@isnad1 id=eq.0h2v.s6.cc10a83094d7 from=translated src=- shape=b8ae96e3 vocab=2739af2d
-/
theorem solution {W : Type*} [CommRing W] (π : W) :
    chartHom π PowerSeries.X = S π :=
  by
  rw [chartHom_apply, PowerSeries.subst_X (hasSubst_sAmbient W), sAmbient, map_add, S_def]
  rfl
