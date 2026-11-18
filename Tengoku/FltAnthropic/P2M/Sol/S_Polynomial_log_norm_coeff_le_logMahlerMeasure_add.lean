import Tengoku.Seed.Analysis.Polynomial.MahlerMeasure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Polynomial_log_norm_coeff_le_logMahlerMeasure_add.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open_scoped`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Polynomial_log_norm_coeff_le_logMahlerMeasure_add

namespace Polynomial export _root_.Polynomial (logMahlerMeasure_eq_log_MahlerMeasure coeff natDegree logMahlerMeasure mahlerMeasure_pos_of_ne_zero le_natDegree_of_ne_zero mahlerMeasure norm_coeff_le_choose_mul_mahlerMeasure) end Polynomial
open scoped _root_.Polynomial in

theorem Polynomial.log_norm_coeff_le_logMahlerMeasure_add' {p : Polynomial ℂ} {k : ℕ}
    (hk : p.coeff k ≠ 0) :
    Real.log ‖p.coeff k‖ ≤ p.logMahlerMeasure + p.natDegree * Real.log 2 := by
  have hp : p ≠ 0 := fun h ↦ hk (by simp [h])
  have hkn : k ≤ p.natDegree := Polynomial.le_natDegree_of_ne_zero hk
  have hchoose : (0 : ℝ) < p.natDegree.choose k := by exact_mod_cast Nat.choose_pos hkn
  have h1 := p.norm_coeff_le_choose_mul_mahlerMeasure k
  have hM := p.mahlerMeasure_pos_of_ne_zero hp
  calc Real.log ‖p.coeff k‖
      ≤ Real.log (p.natDegree.choose k * p.mahlerMeasure) :=
        Real.log_le_log (norm_pos_iff.mpr hk) h1
    _ = Real.log (p.natDegree.choose k) + p.logMahlerMeasure := by
        rw [Real.log_mul hchoose.ne' hM.ne', p.logMahlerMeasure_eq_log_MahlerMeasure]
    _ ≤ p.natDegree * Real.log 2 + p.logMahlerMeasure := by
        gcongr
        rw [← Real.log_pow]
        exact Real.log_le_log hchoose (by exact_mod_cast Nat.choose_le_two_pow _ _)
    _ = _ := add_comm _ _

theorem solution {p : Polynomial ℂ} {k : ℕ} (hk : p.coeff k ≠ 0) :
    Real.log ‖p.coeff k‖ ≤ p.logMahlerMeasure + p.natDegree * Real.log 2 :=
  Polynomial.log_norm_coeff_le_logMahlerMeasure_add' hk
