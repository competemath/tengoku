import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_order_coeffEmb.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_order_coeffEmb

open ModularCurve

theorem solution (L : Type*) [Field L] [Algebra ℚ L] (x : LaurentSeries ℚ) : (coeffEmb L x).order = x.order := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, HahnSeries.order_zero, HahnSeries.order_zero]
  have hLx : coeffEmb L x ≠ 0 := by
    intro h0
    have h1 : (coeffEmb L x).coeff x.order = 0 := by rw [h0]; rfl
    rw [coeffEmb_coeff, map_eq_zero_iff _ (algebraMap ℚ L).injective] at h1
    exact HahnSeries.coeff_order_eq_zero.not.mpr hx h1
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero ?_)
    (HahnSeries.order_le_of_coeff_ne_zero ?_)
  · rw [coeffEmb_coeff]
    exact fun h => HahnSeries.coeff_order_eq_zero.not.mpr hx
      ((map_eq_zero_iff _ (algebraMap ℚ L).injective).mp h)
  · intro h
    exact HahnSeries.coeff_order_eq_zero.not.mpr hLx (by rw [coeffEmb_coeff, h, map_zero])
