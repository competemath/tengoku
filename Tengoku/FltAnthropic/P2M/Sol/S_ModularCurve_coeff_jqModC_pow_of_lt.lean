import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_JqCoeff
import Tengoku.Seed.RingTheory.Algebraic.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_coeff_jqModC_pow_of_lt.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_coeff_jqModC_pow_of_lt

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
@isnad1 id=eq.1h3v.s7.92fe4cf9b0a8 from=translated src=- shape=d2e98f52 vocab=44e1e1ad
-/
theorem coeff_jqModC_pow_of_lt {n : ℕ} {m : ℤ} (hm : m < -(n : ℤ)) : ((jqModC K) ^ n).coeff m = 0 := by
  rw [jqModC_pow, HahnSeries.coeff_single_mul, one_mul]
  exact ofPowerSeries_coeff_of_neg _ (by omega)

end CharLRows

end ModularCurve
end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_coeff_jqModC_pow_of_lt.ModularCurve in
/--
@isnad1 id=eq.1h3v.s7.92fe4cf9b0a8 from=translated src=- shape=d2e98f52 vocab=44e1e1ad
-/
theorem solution (K : Type*) [CommRing K] {b : ℕ} {m : ℤ} (hm : m < -(b : ℤ)) :
    ((jqModC K) ^ b).coeff m = 0 :=
  CharLRows.coeff_jqModC_pow_of_lt K hm
