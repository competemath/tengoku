import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_AnalyticOnNhd_log_norm_le_circleAverage_log_norm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AnalyticOnNhd_log_norm_sub_mul_le_circleAverage.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AnalyticOnNhd_log_norm_sub_mul_le_circleAverage

open Real MeasureTheory Metric

/--
@isnad1 id=le.5h6v.s7.6ee0d802a235 from=translated src=- shape=0536e8a3 vocab=5847142a
-/
theorem solution {F : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall c |R|)) (hc : F c ≠ 0) {g : ℂ → ℝ} {k M : ℝ}
    (hg : CircleIntegrable g c R) (hM : ∀ z ∈ Metric.sphere c |R|, g z ≤ M) (hk : 0 ≤ k) :
    Real.log ‖F c‖ - k * M ≤ Real.circleAverage (fun z ↦ Real.log ‖F z‖ - k * g z) c R := by
  have hFi : CircleIntegrable (fun z ↦ Real.log ‖F z‖) c R :=
    MeromorphicOn.circleIntegrable_log_norm (hF.mono Metric.sphere_subset_closedBall).meromorphicOn
  have hgi : CircleIntegrable (fun z ↦ k * g z) c R := by
    simpa [smul_eq_mul] using hg.const_fun_smul (a := k)
  rw [Real.circleAverage_fun_sub hFi hgi]
  have h1 := hF.log_norm_le_circleAverage_log_norm hc
  have h2 : Real.circleAverage (fun z ↦ k * g z) c R ≤ k * M := by
    have h3 : Real.circleAverage (fun z ↦ k * g z) c R = k * Real.circleAverage g c R := by
      simpa [smul_eq_mul] using Real.circleAverage_fun_smul (f := g) (c := c) (R := R) (a := k)
    rw [h3]
    exact mul_le_mul_of_nonneg_left (Real.circleAverage_mono_on_of_le_circle hg hM) hk
  linarith
