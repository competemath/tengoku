import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open HahnSeries

namespace ModularCurve

def IsMonicOfOrder (f : LaurentSeries ℚ) (m : ℤ) : Prop :=
  f.order = m ∧ f.leadingCoeff = 1

namespace IsMonicOfOrder

/--
@isnad1 id=ismonico.1h1v.s7.1b44c9d8e33f from=translated src=- shape=486b3e33 vocab=a1664b3d
-/
theorem ofPowerSeries {U : PowerSeries ℚ} (hU : PowerSeries.constantCoeff U = 1) :
    IsMonicOfOrder (HahnSeries.ofPowerSeries ℤ ℚ U) 0 := by
  have hcoeff0 : (HahnSeries.ofPowerSeries ℤ ℚ U).coeff (0 : ℤ) = 1 := by
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_zero_eq_constantCoeff, hU]
  have hne0 : (HahnSeries.ofPowerSeries ℤ ℚ U).coeff (0 : ℤ) ≠ 0 := by
    rw [hcoeff0]; exact one_ne_zero
  have hne : HahnSeries.ofPowerSeries ℤ ℚ U ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero hne0
  have horder : (HahnSeries.ofPowerSeries ℤ ℚ U).order = 0 := by
    refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hne0) ?_
    by_contra hlt
    rw [not_le] at hlt
    exact hne (HahnSeries.coeff_order_eq_zero.mp
      (ModularCurve.ofPowerSeries_coeff_of_neg U hlt))
  exact ⟨horder, by rw [HahnSeries.leadingCoeff_eq, horder, hcoeff0]⟩

end IsMonicOfOrder

section ModularUnit

variable (p : ℕ) [NeZero p]

end ModularUnit

end ModularCurve

end
