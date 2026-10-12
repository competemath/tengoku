import Tengoku.OpenaiMath.OAI.Probability.ProjectionMoments.FrameMoments

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[fun_prop] lemma measurable_rieszKernel [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (α : ℝ) (z : E) : Measurable (rieszKernel α z) := by
  unfold rieszKernel
  fun_prop

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rieszKernel_le_inverse_nat [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {α : ℝ} (hα : 0 ≤ α) {m : ℕ} (hm : α ≤ m)
    (z s : E) (hneq : s ≠ z) :
    rieszKernel α z s ≤ 1 + ENNReal.ofReal (‖s-z‖⁻¹^m) := by
  have hn : 0 < ‖s-z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hneq)
  by_cases h1 : 1 ≤ ‖s-z‖
  · apply le_add_of_le_left
    simpa only [rieszKernel, ENNReal.rpow_zero] using ENNReal.rpow_le_rpow_of_exponent_le
      (ENNReal.one_le_ofReal.mpr h1) (show -α ≤ 0 by linarith)
  · have hh := ENNReal.rpow_le_rpow_of_exponent_ge
      (show ENNReal.ofReal ‖s-z‖ ≤ 1 by exact ENNReal.ofReal_le_one.mpr (le_of_not_ge h1))
      (show -(m:ℝ) ≤ -α by linarith)
    have he : (ENNReal.ofReal ‖s-z‖)^(-(m:ℝ)) = ENNReal.ofReal (‖s-z‖⁻¹^m) := by
      rw [ENNReal.rpow_neg,ENNReal.rpow_natCast,ENNReal.ofReal_pow (inv_nonneg.mpr hn.le),
        ENNReal.ofReal_inv_of_pos hn,ENNReal.inv_pow]
    exact hh.trans (by rw [he]; exact le_add_left le_rfl)

lemma rieszPotential_ball_control [Nontrivial E] {α : ℝ} (hα : 0 ≤ α)
    {h : E → ℝ≥0∞} (hh : Measurable h) (z : E) {r : ℝ} (hr : 0 < r) :
    (NoiselessRegression.ambientSphereLaw.withDensity h) (Metric.closedBall z r) ≤
      rieszPotential α h * ENNReal.ofReal (r^α) := by
  have hr0 : ENNReal.ofReal r ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hr)
  have hrt : ENNReal.ofReal r ≠ ∞ := ENNReal.ofReal_ne_top
  have hnorm (s : E) (hs : s ∈ Metric.closedBall z r) :
      1 ≤ ENNReal.ofReal (r^α) * rieszKernel α z s := by
    have hs' : ‖s-z‖ ≤ r := by simpa [dist_eq_norm] using hs
    have hb := ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hs') hα
    rw [rieszKernel, ENNReal.rpow_neg, ← ENNReal.ofReal_rpow_of_pos hr]
    calc
      _ = (ENNReal.ofReal r)^α*((ENNReal.ofReal r)^α)⁻¹ :=
        (ENNReal.mul_inv_cancel (ne_of_gt (ENNReal.rpow_pos (bot_lt_iff_ne_bot.mpr hr0) hrt)) (ENNReal.rpow_ne_top_of_nonneg hα hrt)).symm
      _ ≤ _ := mul_le_mul' le_rfl (ENNReal.inv_le_inv.mpr hb)
  rw [withDensity_apply _ Metric.isClosed_closedBall.measurableSet]
  calc
    _ ≤ ∫⁻ s in Metric.closedBall z r, ENNReal.ofReal (r^α)*(h s*rieszKernel α z s)
        ∂NoiselessRegression.ambientSphereLaw := by
      apply setLIntegral_mono' Metric.isClosed_closedBall.measurableSet
      intro s hs
      simpa only [mul_one,mul_left_comm] using mul_le_mul' le_rfl (hnorm s hs)
    _ ≤ ∫⁻ s, ENNReal.ofReal (r^α)*(h s*rieszKernel α z s)
        ∂NoiselessRegression.ambientSphereLaw := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (r^α)*(∫⁻ s, h s*rieszKernel α z s ∂NoiselessRegression.ambientSphereLaw) :=
      lintegral_const_mul _ (hh.mul (measurable_rieszKernel α z))
    _ ≤ _ := by rw [mul_comm]; exact mul_le_mul' (show _ ≤ rieszPotential α h from le_iSup (fun z => ∫⁻ s, h s*rieszKernel α z s ∂NoiselessRegression.ambientSphereLaw) z) le_rfl

end ProjectionMoments

end

end OAI
