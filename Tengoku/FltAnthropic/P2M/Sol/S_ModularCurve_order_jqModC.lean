import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_JqCoeff
import Tengoku.Seed.RingTheory.Algebraic.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_order_jqModC.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_order_jqModC

noncomputable section
open HahnSeries

namespace ModularCurve
export _root_.ModularCurve (jqModC jNum constantCoeff_jNum ofPowerSeries_coeff_of_neg jq_pow)
open _root_.ModularCurve
namespace CharLRows

variable (K : Type*) [CommRing K]

theorem jqModC_pow (n : ℕ) :
    (jqModC K) ^ n = HahnSeries.single (-(n : ℤ)) 1 *
      HahnSeries.ofPowerSeries ℤ K ((jNum.map (Int.castRingHom K)) ^ n) := by
  have h : n • (-1 : ℤ) = -(n : ℤ) := by simp
  rw [jqModC, mul_pow, HahnSeries.single_pow, one_pow, h, ← map_pow]

theorem constantCoeff_jNum_map : PowerSeries.constantCoeff (jNum.map (Int.castRingHom K)) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
    constantCoeff_jNum, map_one]

theorem coeff_jqModC_pow_self (n : ℕ) : ((jqModC K) ^ n).coeff (-(n : ℤ)) = 1 := by
  rw [jqModC_pow, HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add, neg_add_cancel,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff, map_pow, constantCoeff_jNum_map, one_pow]

theorem coeff_jqModC_pow_of_lt {n : ℕ} {m : ℤ} (hm : m < -(n : ℤ)) : ((jqModC K) ^ n).coeff m = 0 := by
  rw [jqModC_pow, HahnSeries.coeff_single_mul, one_mul]
  exact ofPowerSeries_coeff_of_neg _ (by omega)

theorem coeff_jqModC_neg_one : (jqModC K).coeff (-1 : ℤ) = 1 := by
  simpa using coeff_jqModC_pow_self K 1

theorem jqModC_ne_zero [Nontrivial K] : jqModC K ≠ 0 := by
  intro h
  have h1 : (jqModC K).coeff (-1 : ℤ) = 1 := coeff_jqModC_neg_one K
  rw [h, HahnSeries.coeff_zero] at h1
  exact zero_ne_one h1

theorem order_jqModC [Nontrivial K] : (jqModC K).order = -1 := by
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero ?_) ?_
  · rw [coeff_jqModC_neg_one]
    exact one_ne_zero
  · by_contra hlt
    rw [not_le] at hlt
    refine HahnSeries.coeff_order_eq_zero.not.mpr (jqModC_ne_zero K) ?_
    have h := coeff_jqModC_pow_of_lt K (n := 1) (m := (jqModC K).order)
      (by simpa using hlt)
    simpa using h

end CharLRows

end ModularCurve
end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_order_jqModC.ModularCurve in
theorem solution (K : Type*) [CommRing K] [Nontrivial K] :
    (jqModC K).order = -1 :=
  CharLRows.order_jqModC K
