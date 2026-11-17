import Tengoku.Seed.RingTheory.PowerSeries.Basic
import Tengoku.Seed.Algebra.BigOperators.Ring.Finset
import Tengoku.FltAnthropic.Definitions.Def_ModularForm_EisensteinChiNegThree

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_EisensteinWeightOne_three_dvd_coeff_mul_e1Chi3_sub.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_EisensteinWeightOne_three_dvd_coeff_mul_e1Chi3_sub

namespace EisensteinWeightOne
export _root_.EisensteinWeightOne (chiNegThree sigmaChi e1Chi3)
open _root_.EisensteinWeightOne

private theorem coeff_e1Chi3_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    PowerSeries.coeff n e1Chi3 = 6 * sigmaChi n := by
  rw [e1Chi3, PowerSeries.coeff_mk, ite_eq_right hn]

private theorem three_dvd_coeff_e1Chi3_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (3 : ℤ) ∣ PowerSeries.coeff n e1Chi3 :=
  ⟨2 * sigmaChi n, by rw [coeff_e1Chi3_of_ne_zero hn]; ring⟩

end EisensteinWeightOne

open _root_.EisensteinWeightOne open _root_.P2MW.S_EisensteinWeightOne_three_dvd_coeff_mul_e1Chi3_sub.EisensteinWeightOne

private theorem three_dvd_coeff_e1Chi3_sub_one' (n : ℕ) :
    (3 : ℤ) ∣ PowerSeries.coeff n (e1Chi3 - 1) := by
  rw [map_sub, PowerSeries.coeff_one]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [e1Chi3, PowerSeries.coeff_mk]
  · rw [ite_eq_right hn, sub_zero]
    exact three_dvd_coeff_e1Chi3_of_ne_zero hn

/--
@isnad1 id=dvd.0h2v.s7.a641bce5173a from=translated src=- shape=eb274cd6 vocab=3cf9a5d3
-/
theorem solution (g : PowerSeries ℤ) (n : ℕ) :
    (3 : ℤ) ∣ PowerSeries.coeff n (g * e1Chi3) - PowerSeries.coeff n g := by
  have hfactor : g * e1Chi3 - g = g * (e1Chi3 - 1) := by ring
  rw [← map_sub, hfactor, PowerSeries.coeff_mul]
  exact Finset.dvd_sum fun p _ => (three_dvd_coeff_e1Chi3_sub_one' p.2).mul_left _
