import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingModel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

universe u

namespace ModularCurve.UVCrossingModel

noncomputable section

variable {W : Type u} [CommRing W]

def inU (a : PowerSeries W) : MvPowerSeries (Fin 2) W :=
  fun d => if d 1 = 0 then PowerSeries.coeff (d 0) a else 0

def inV (b : PowerSeries W) : MvPowerSeries (Fin 2) W :=
  fun d => if d 0 = 0 then PowerSeries.coeff (d 1) b else 0

/--
@isnad1 id=eq.0h3v.s9.df455cf7c36b from=translated src=- shape=35de2157 vocab=e260c6cd
-/
theorem coeff_inU (a : PowerSeries W) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (inU a) = if d 1 = 0 then PowerSeries.coeff (d 0) a else 0 := rfl

/--
@isnad1 id=eq.0h3v.s9.c9628ac70fa9 from=translated src=- shape=35de2157 vocab=92e7cbf9
-/
theorem coeff_inV (b : PowerSeries W) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (inV b) = if d 0 = 0 then PowerSeries.coeff (d 1) b else 0 := rfl

def annulusWeight (e t : ℕ) (d : Fin 2 →₀ ℕ) : ℕ := d 0 * t + d 1 * (e - t)

def repGaussOrder (v : W → ℕ∞) (e t : ℕ) (F : MvPowerSeries (Fin 2) W) : ℕ∞ :=
  ⨅ d : Fin 2 →₀ ℕ, v (MvPowerSeries.coeff d F) + (annulusWeight e t d : ℕ∞)

def gaussOrder (v : W → ℕ∞) (π : W) (e t : ℕ) (x : UVCrossingModel W π) : ℕ∞ :=
  ⨆ F ∈ {F : MvPowerSeries (Fin 2) W | mk π F = x}, repGaussOrder v e t F

/--
@isnad1 id=le.0h6v.s8.7ff394b66e90 from=translated src=- shape=cd0f508a vocab=67924846
-/
theorem repGaussOrder_le (v : W → ℕ∞) (e t : ℕ) (F : MvPowerSeries (Fin 2) W) (d : Fin 2 →₀ ℕ) :
    repGaussOrder v e t F ≤ v (MvPowerSeries.coeff d F) + (annulusWeight e t d : ℕ∞) :=
  iInf_le _ d

/--
@isnad1 id=iff.0h6v.s8.9c4c81d60397 from=translated src=- shape=3a919a71 vocab=67924846
-/
theorem le_repGaussOrder_iff (v : W → ℕ∞) (e t : ℕ) (F : MvPowerSeries (Fin 2) W) (n : ℕ∞) :
    n ≤ repGaussOrder v e t F ↔ ∀ d, n ≤ v (MvPowerSeries.coeff d F) + (annulusWeight e t d : ℕ∞) :=
  le_iInf_iff

/--
@isnad1 id=le.0h6v.s7.78affa7406d8 from=translated src=- shape=23d81957 vocab=9bf97205
-/
theorem repGaussOrder_le_gaussOrder (v : W → ℕ∞) (π : W) (e t : ℕ) (F : MvPowerSeries (Fin 2) W) :
    repGaussOrder v e t F ≤ gaussOrder v π e t (mk π F) :=
  le_iSup₂ (f := fun G (_ : G ∈ {G : MvPowerSeries (Fin 2) W | mk π G = mk π F}) => repGaussOrder v e t G) F rfl

/--
@isnad1 id=iff.0h7v.s7.aed7bccf04c0 from=translated src=- shape=e1778378 vocab=9bf97205
-/
theorem gaussOrder_le_iff (v : W → ℕ∞) (π : W) (e t : ℕ) (x : UVCrossingModel W π) (n : ℕ∞) :
    gaussOrder v π e t x ≤ n ↔ ∀ F, mk π F = x → repGaussOrder v e t F ≤ n :=
  iSup₂_le_iff

end

end ModularCurve.UVCrossingModel
