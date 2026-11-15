import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingModel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

universe u

namespace ModularCurve

noncomputable section

namespace UVCrossingModel

section AmbientChart

variable (W : Type u) [CommRing W]

def sAmbient : MvPowerSeries (Fin 2) W :=
  MvPowerSeries.X 0 + MvPowerSeries.X 1

/--
@isnad1 id=eq.0h1v.s7.87bac7c5dadf from=translated src=- shape=259f0c16 vocab=abde5987
-/
theorem sAmbient_def :
    sAmbient W = MvPowerSeries.X 0 + MvPowerSeries.X 1 :=
  rfl

/--
@isnad1 id=eq.0h1v.s7.aba95ee3cadb from=translated src=- shape=5a08073f vocab=19a2e9c0
-/
theorem constantCoeff_sAmbient : MvPowerSeries.constantCoeff (sAmbient W) = 0 := by
  rw [sAmbient, map_add, MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_X,
    add_zero]

/--
@isnad1 id=hassubst.0h1v.s4.a764476122e3 from=translated src=- shape=5e04a8bc vocab=b8b83bfc
-/
theorem hasSubst_sAmbient : PowerSeries.HasSubst (sAmbient W) :=
  PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_sAmbient W)

end AmbientChart

variable {W : Type u} [CommRing W]

def chartHom (π : W) : PowerSeries W →+* UVCrossingModel W π :=
  (mk π).comp (PowerSeries.substAlgHom (hasSubst_sAmbient W)).toRingHom

/--
@isnad1 id=eq.0h3v.s8.038b0ddb133b from=translated src=- shape=921c400b vocab=3e2bb284
-/
theorem chartHom_apply (π : W) (f : PowerSeries W) :
    chartHom π f = mk π (PowerSeries.subst (sAmbient W) f) := by
  show mk π ((PowerSeries.substAlgHom (hasSubst_sAmbient W)) f) = _
  rw [PowerSeries.coe_substAlgHom]

end UVCrossingModel

end

end ModularCurve
