import Tengoku.Seed.Analysis.Polynomial.MahlerMeasure
import Tengoku.FltAnthropic.P2M.Sol.S_Polynomial_log_norm_coeff_le_logMahlerMeasure_add

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Polynomial_log_norm_coeff_le_logMahlerMeasure_add.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem Polynomial.log_norm_coeff_le_logMahlerMeasure_add {p : Polynomial ℂ} {k : ℕ} (hk : p.coeff k ≠ 0) :
    Real.log ‖p.coeff k‖ ≤ p.logMahlerMeasure + p.natDegree * Real.log 2 := by exact @_root_.P2MW.S_Polynomial_log_norm_coeff_le_logMahlerMeasure_add.solution p k hk
