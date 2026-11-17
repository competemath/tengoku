import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AnalyticOnNhd_log_norm_le_circleAverage_log_norm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AnalyticOnNhd_log_norm_le_circleAverage_log_norm.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem AnalyticOnNhd.log_norm_le_circleAverage_log_norm {F : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall c |R|)) (hc : F c ≠ 0) :
    Real.log ‖F c‖ ≤ Real.circleAverage (fun z ↦ Real.log ‖F z‖) c R := by exact @_root_.P2MW.S_AnalyticOnNhd_log_norm_le_circleAverage_log_norm.solution F c R hF hc
