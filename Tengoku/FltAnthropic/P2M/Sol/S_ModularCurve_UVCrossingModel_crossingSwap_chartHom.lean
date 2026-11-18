import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingChart

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_UVCrossingModel_crossingSwap_chartHom.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_UVCrossingModel_crossingSwap_chartHom

open ModularCurve ModularCurve.UVCrossingModel in
/--
@isnad1 id=eq.0h3v.s9.976d6e8990be from=translated src=- shape=a2250800 vocab=1517bf2c
-/
theorem solution {W : Type*} [CommRing W] (π : W) (f : PowerSeries W) :
    crossingSwap π (chartHom π f) = chartHom π f :=
  by
  have hsw : ∀ f : PowerSeries W, uvSwapEquiv (PowerSeries.subst (sAmbient W) f) = PowerSeries.subst (sAmbient W) f := by
    intro f
    rw [uvSwapEquiv_apply, MvPowerSeries.rename_eq_subst, PowerSeries.subst_def,
      MvPowerSeries.subst_comp_subst_apply
        (PowerSeries.HasSubst.const (hasSubst_sAmbient W))
        (MvPowerSeries.HasSubst.X_comp _)]
    have h : (fun _ : Unit ↦ MvPowerSeries.subst
        (MvPowerSeries.X ∘ ⇑(Equiv.swap (0 : Fin 2) 1)) (sAmbient W)) =
        (fun _ : Unit ↦ sAmbient W) := by
      funext _
      rw [← MvPowerSeries.rename_eq_subst, ← uvSwapEquiv_apply]
      rw [sAmbient, map_add, uvSwapEquiv_X_zero, uvSwapEquiv_X_one, add_comm]
    rw [h, ← PowerSeries.subst_def]
  rw [chartHom_apply, crossingSwap_mk, hsw]
