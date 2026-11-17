import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Complex_volume_ball_inter_exists_sum_mul_eq_zero_le

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Complex_volume_ball_inter_exists_sum_mul_eq_zero_le.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open MeasureTheory Metric
/--
@isnad1 id=le.2h5v.s9.fd2ac040be22 from=translated src=- shape=f85bcce1 vocab=059e85f5
-/
theorem Complex.volume_ball_inter_exists_sum_mul_eq_zero_le {n : ℕ} (c : ℂ → Fin n → ℂ) (z₀ : ℂ) (K : Set ℂ)
    (hc : c z₀ ≠ 0) {δ : ℝ} (hδ : ∀ z ∈ K, ‖c z - c z₀‖ ≤ δ) :
    volume {b : Fin n → ℂ | b ∈ Metric.ball 0 1 ∧ ∃ z ∈ K, ∑ j, b j * c z j = 0}
      ≤ ENNReal.ofReal ((n * δ / ‖c z₀‖) ^ 2) * volume (Metric.ball (0 : Fin n → ℂ) 1) := by exact @_root_.P2MW.S_Complex_volume_ball_inter_exists_sum_mul_eq_zero_le.solution n c z₀ K hc δ hδ
