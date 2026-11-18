import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_QExpansionDiff
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_thetaL_coeffMap_eq_coeffMap_single_mul_derivative.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_thetaL_coeffMap_eq_coeffMap_single_mul_derivative

namespace ModularCurve
export _root_.ModularCurve (thetaL thetaL_apply coeffMap coeffMap_coeff)
open _root_.ModularCurve

section

variable {R K : Type*} [CommRing R] [Field K]

private theorem coeffMap_single_one (φ : R →+* K) :
    coeffMap φ (HahnSeries.single (1 : ℤ) (1 : R)) = HahnSeries.single (1 : ℤ) (1 : K) := by
  ext n
  rw [coeffMap_coeff, HahnSeries.coeff_single, HahnSeries.coeff_single]
  split_ifs <;> simp

private theorem derivative_coeffMap (φ : R →+* K) (w : LaurentSeries R) :
    LaurentSeries.derivative K (coeffMap φ w) = coeffMap φ (LaurentSeries.derivative R w) := by
  ext n
  rw [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff, coeffMap_coeff,
    coeffMap_coeff, LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff, map_zsmul]

private theorem thetaL_coeffMap_impl (φ : R →+* K) (w : LaurentSeries R) :
    thetaL K (coeffMap φ w) =
      coeffMap φ (HahnSeries.single (1 : ℤ) (1 : R) * LaurentSeries.derivative R w) := by
  rw [thetaL_apply, derivative_coeffMap, map_mul, coeffMap_single_one]

end

end ModularCurve

theorem solution {R : Type*} [CommRing R]
    {K : Type*} [Field K] (φ : R →+* K) (w : LaurentSeries R) :
    ModularCurve.thetaL K (ModularCurve.coeffMap φ w) =
      ModularCurve.coeffMap φ (HahnSeries.single (1 : ℤ) (1 : R) * LaurentSeries.derivative R w) :=
  ModularCurve.thetaL_coeffMap_impl φ w
