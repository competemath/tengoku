import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_JqCoeff
import Tengoku.Seed.RingTheory.Algebraic.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_coeff_jqModC_neg_one.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_coeff_jqModC_neg_one

noncomputable section
open HahnSeries

namespace ModularCurve
export _root_.ModularCurve (jqModC jNum constantCoeff_jNum ofPowerSeries_coeff_of_neg jq_pow)
open _root_.ModularCurve
namespace CharLRows

variable (K : Type*) [CommRing K]

/--
@isnad1 id=eq.0h2v.s9.4d056bb05dde from=translated src=- shape=0f562fe2 vocab=a77d08de
-/
theorem jqModC_pow (n : ℕ) :
    (jqModC K) ^ n = HahnSeries.single (-(n : ℤ)) 1 *
      HahnSeries.ofPowerSeries ℤ K ((jNum.map (Int.castRingHom K)) ^ n) := by
  have h : n • (-1 : ℤ) = -(n : ℤ) := by simp
  rw [jqModC, mul_pow, HahnSeries.single_pow, one_pow, h, ← map_pow]

/--
@isnad1 id=eq.0h1v.s7.77982d5a5a39 from=translated src=- shape=3f75c59f vocab=f0bbd359
-/
theorem constantCoeff_jNum_map : PowerSeries.constantCoeff (jNum.map (Int.castRingHom K)) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
    constantCoeff_jNum, map_one]

/--
@isnad1 id=eq.0h2v.s7.12f922058688 from=translated src=- shape=91cba0af vocab=d662f486
-/
theorem coeff_jqModC_pow_self (n : ℕ) : ((jqModC K) ^ n).coeff (-(n : ℤ)) = 1 := by
  rw [jqModC_pow, HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add, neg_add_cancel,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff, map_pow, constantCoeff_jNum_map, one_pow]

/--
@isnad1 id=eq.0h1v.s5.a4a649af0e6d from=translated src=- shape=21dd8601 vocab=e3586c72
-/
theorem coeff_jqModC_neg_one : (jqModC K).coeff (-1 : ℤ) = 1 := by
  simpa using coeff_jqModC_pow_self K 1

end CharLRows

end ModularCurve
end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_coeff_jqModC_neg_one.ModularCurve in
/--
@isnad1 id=eq.0h1v.s5.a4a649af0e6d from=translated src=- shape=21dd8601 vocab=e3586c72
-/
theorem solution (K : Type*) [CommRing K] :
    (jqModC K).coeff (-1 : ℤ) = 1 :=
  CharLRows.coeff_jqModC_neg_one K
