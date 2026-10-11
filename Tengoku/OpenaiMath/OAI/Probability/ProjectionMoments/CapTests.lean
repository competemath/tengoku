import Tengoku.OpenaiMath.OAI.Probability.ProjectionMoments.Caps

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma cap_ratio_algebra (d n : ℕ) {r ρ α : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hα : 2*α = n) :
    (r^n)⁻¹ * (16:ℝ)^d * (3*4^d*ρ^n) * (r/ρ)^α =
      3*64^d*(ρ/r)^α := by
  have hre : r^n = (r^α)^2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hr.le]
    congr 1
    norm_num only [Nat.cast_ofNat]
    linarith
  have hρe : ρ^n = (ρ^α)^2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hρ.le]
    congr 1
    norm_num only [Nat.cast_ofNat]
    linarith
  rw [hre,hρe,Real.div_rpow hr.le hρ.le, Real.div_rpow hρ.le hr.le]
  have hc : (16:ℝ)^d * 4^d = 64^d := by rw [← mul_pow]; norm_num
  field_simp [(Real.rpow_pos_of_pos hr α).ne', (Real.rpow_pos_of_pos hρ α).ne']
  nlinarith [hc]

lemma cap_small_scale_constant (d : ℕ) (hd : 1 ≤ d) {α ρ r t : ℝ}
    (hα0 : 0 ≤ α) (hαd : α ≤ d) (hr : 0 < r) (ht : 0 < t)
    (hρ : 0 ≤ ρ) (hρt : ρ ≤ 8*r*t) :
    3*64^d*(ρ/r)^α ≤ (2048:ℝ)^d*t^α := by
  have hratio : ρ/r ≤ 8*t := (div_le_iff₀ hr).mpr (by nlinarith)
  have h8 : (8:ℝ)^α ≤ (8:ℝ)^(d:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hαd
  have h3 : (3:ℝ) ≤ 3^d := by simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 3) hd
  calc
    _ ≤ 3*64^d*(8*t)^α := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (div_nonneg hρ hr.le) hratio hα0) (by positivity)
    _ = 3*64^d*8^α*t^α := by rw [Real.mul_rpow (by norm_num) ht.le]; ring
    _ ≤ 3^d*64^d*8^d*t^α := by rw [Real.rpow_natCast] at h8; gcongr
    _ = (1536:ℝ)^d*t^α := by rw [← mul_pow, ← mul_pow]; norm_num
    _ ≤ _ := by gcongr; norm_num

def capTestMeasure (h : E → ℝ≥0∞) (c : E) (r : ℝ) : Measure E :=
  ((capMeasure c r).withDensity h).map (rescale c r)

lemma capTestMeasure_mass {h : E → ℝ≥0∞} {c : E} {r α : ℝ} (hr : 0 < r)
    (D : CapDictionary c r α)
    (hdual : ∀ i, ∫⁻ x, h x ∂capMeasure (D.center i) (D.radius i) ≤ ENNReal.ofReal ((r/D.radius i)^α)) :
    capTestMeasure h c r Set.univ ≤ 1 := by
  have hp := hdual D.parent
  rw [D.parent_center,D.parent_radius,div_self hr.ne',Real.one_rpow,ENNReal.ofReal_one] at hp
  simpa only [capTestMeasure,Measure.map_apply (measurable_rescale c r) MeasurableSet.univ,
    Set.preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hp

lemma capTestMeasure_finite {h : E → ℝ≥0∞} {c : E} {r α : ℝ} (hr : 0 < r)
    (D : CapDictionary c r α)
    (hdual : ∀ i, ∫⁻ x, h x ∂capMeasure (D.center i) (D.radius i) ≤ ENNReal.ofReal ((r/D.radius i)^α)) :
    IsFiniteMeasure (capTestMeasure h c r) :=
  ⟨(capTestMeasure_mass hr D hdual).trans_lt (by simp)⟩

lemma capTestMeasure_support (h : E → ℝ≥0∞) (c : E) {r : ℝ} (hr : 0 < r) :
    (capTestMeasure h c r).support ⊆ Metric.closedBall 0 1 := by
  apply Measure.support_subset_of_isClosed Metric.isClosed_closedBall
  apply (ae_map_iff (measurable_rescale c r).aemeasurable Metric.isClosed_closedBall.measurableSet).mpr
  filter_upwards [((capMeasure c r).withDensity h).support_mem_ae] with x hx
  have hx' := capMeasure_support c r ((withDensity_absolutelyContinuous (capMeasure c r) h).support_mono hx)
  change x ∈ rescale c r ⁻¹' Metric.closedBall 0 1
  rw [rescale_preimage_closedBall c 0 hr, dilate, smul_zero, zero_add, mul_one]
  exact hx'

lemma capTestMeasure_ball (h : E → ℝ≥0∞) (c : E) {r : ℝ} (hr : 0 < r) (b : E) (t : ℝ) :
    capTestMeasure h c r (Metric.closedBall b t) =
      (NoiselessRegression.ambientSphereLaw (Metric.closedBall c r))⁻¹ *
        (NoiselessRegression.ambientSphereLaw.withDensity h)
          (Metric.closedBall (dilate c r b) (r*t) ∩ Metric.closedBall c r) := by
  rw [capTestMeasure, Measure.map_apply (measurable_rescale c r) Metric.isClosed_closedBall.measurableSet,
    rescale_preimage_closedBall c b hr, capMeasure, withDensity_smul_measure,
    Measure.smul_apply, smul_eq_mul, ← restrict_withDensity Metric.isClosed_closedBall.measurableSet,
    Measure.restrict_apply Metric.isClosed_closedBall.measurableSet]

end ProjectionMoments

end

end OAI
