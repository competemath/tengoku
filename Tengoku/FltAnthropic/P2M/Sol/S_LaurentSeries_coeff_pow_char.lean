import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0
import Tengoku.FltAnthropic.Theorems.Thm_ModularCurve_pow_char_eq_map_frobenius_qExpand

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LaurentSeries_coeff_pow_char.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LaurentSeries_coeff_pow_char

set_option autoImplicit false

open HahnSeries ModularCurve

theorem solution {R : Type*} [CommRing R] (q : ℕ) [Fact q.Prime] [CharP R q]
    (f : LaurentSeries R) (n : ℤ) :
    (f ^ q).coeff n = if (q : ℤ) ∣ n then f.coeff (n / q) ^ q else 0 := by
  rw [pow_char_eq_map_frobenius_qExpand q f, HahnSeries.map_coeff]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
    rw [qExpand_coeff_mul, Int.mul_ediv_cancel_left _ hq0, frobenius_def]
  · rw [qExpand_coeff_of_not_dvd q f h, map_zero]
