import Tengoku.OpenaiMath.OAI.Probability.ProjectionMoments.Polar

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
attribute [fun_prop] measurable_polarRows
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma unitBallVolume_ne_zero (k : ℕ) : unitBallVolume k ≠ 0 := by
  apply ne_of_gt
  exact (Metric.measure_ball_pos volume 0 one_pos).trans_le (measure_mono Metric.ball_subset_closedBall)
lemma unitBallVolume_ne_top (k : ℕ) : unitBallVolume k ≠ ∞ :=
  (isCompact_closedBall (0 : Label k) (1:ℝ)).measure_ne_top
instance unitBallLaw_probability (k : ℕ) : IsProbabilityMeasure (unitBallLaw k) := by
  constructor
  simp only [unitBallLaw, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (unitBallVolume_ne_zero k) (unitBallVolume_ne_top k)

lemma unitBallVolume_bound (k : ℕ) (hk : 1 ≤ k) :
    unitBallVolume k ≤ ENNReal.ofReal ((6/Real.sqrt k)^k) := by
  rw [unitBallVolume, Measure.addHaar_unitClosedBall_eq_addHaar_unitBall]
  exact unit_ball_volume_bound k hk

lemma normalizedDensity_support (ν : Measure E) [IsFiniteMeasure ν] {k : ℕ}
    {u : Fin k → E} (hu : Orthonormal ℝ u) (hs : ν.support ⊆ Metric.closedBall 0 1)
    (X : Fin k → E) (y : Label k) (hy : 1 < ‖y‖) : normalizedDensity ν k u (X,y) = 0 := by
  have h := lowerDensity_eq_zero_of_far ν k (polarRows u X) 0 1 y hs
    (by simpa only [map_zero, sub_zero, mul_one] using (norm_rowMap_le (polarRows_orthonormal hu X)).trans_lt hy)
  simp only [normalizedDensity, h, mul_zero]

lemma normalizedDensity_is_density (ν : Measure E) [IsFiniteMeasure ν] {k : ℕ}
    {u : Fin k → E} (X : Fin k → E)
    (h : ν.map (rowMap (polarRows u X)) ≪ (volume : Measure (Label k))) :
    ((unitBallVolume k)⁻¹ • (volume : Measure (Label k))).withDensity
      (fun y => normalizedDensity ν k u (X,y)) = ν.map (rowMap (polarRows u X)) := by
  rw [withDensity_smul_measure]
  change (unitBallVolume k)⁻¹ • volume.withDensity
    (unitBallVolume k • (fun y => lowerDensity ν k (polarRows u X,y))) = _
  rw [withDensity_smul _ (by fun_prop), smul_smul,
    ENNReal.inv_mul_cancel (unitBallVolume_ne_zero k) (unitBallVolume_ne_top k), one_smul]
  exact lowerDensity_is_density ν k _ h

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma sphereWeightedRestriction_le [Nontrivial E] {h : E → ℝ≥0∞}
    (h1 : ∀ s, h s ≤ 1) (H : Set E) :
    sphereWeightedRestriction h H ≤ NoiselessRegression.ambientSphereLaw := by
  apply Measure.restrict_le_self.trans
  calc
    _ ≤ NoiselessRegression.ambientSphereLaw.withDensity (1 : E → ℝ≥0∞) :=
      withDensity_mono (Filter.Eventually.of_forall h1)
    _ = _ := withDensity_one

lemma sphereWeightedRestriction_support {h : E → ℝ≥0∞} {H : Set E}
    {z : E} {ρ : ℝ} (hH : H ⊆ Metric.closedBall z ρ) :
    (sphereWeightedRestriction h H).support ⊆ Metric.closedBall z ρ :=
  Measure.support_restrict_subset.trans (fun _ hx =>
    (closure_minimal hH Metric.isClosed_closedBall) hx.1)

end

lemma normalized_cost (d k n : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) (hdk : d ≤ 32*k)
    (D : ℝ) (hD : 0 < D) :
    unitBallVolume k ^ n *
      ((2 : ℝ≥0∞)^k * ENNReal.ofReal (Real.sqrt (2*d))^(k*n) *
        (ENNReal.ofReal (D^d)^(n+1) * (128 : ℝ≥0∞)^(d*n))) ≤
      ENNReal.ofReal ((16384 * max D 1)^(d*(n+1))) := by
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hdR : (d:ℝ) ≤ 32*k := by exact_mod_cast hdk
  have hroot : Real.sqrt (2*d) ≤ 8*Real.sqrt k := by
    have h1 := Real.sq_sqrt (show (0:ℝ) ≤ 2*d by positivity)
    have h2 := Real.sq_sqrt hkR.le
    have h3 := Real.sqrt_nonneg (2*(d:ℝ))
    have h4 := Real.sqrt_pos.mpr hkR
    nlinarith
  have hc : 0 ≤ 6/Real.sqrt k := by positivity
  have hcs : 6/Real.sqrt k * Real.sqrt (2*d) ≤ 48 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (Real.sqrt_pos.mpr hkR)]
    nlinarith
  have hvol : unitBallVolume k ^ n * ENNReal.ofReal (Real.sqrt (2*d))^(k*n) ≤
      (48 : ℝ≥0∞)^(k*n) := by
    calc
      _ ≤ ENNReal.ofReal ((6/Real.sqrt k)^k)^n * ENNReal.ofReal (Real.sqrt (2*d))^(k*n) :=
        mul_le_mul' (pow_le_pow_left' (unitBallVolume_bound k hk) n) le_rfl
      _ = ENNReal.ofReal (6/Real.sqrt k * Real.sqrt (2*d))^(k*n) := by
        rw [ENNReal.ofReal_pow hc, ← pow_mul, ENNReal.ofReal_mul hc, mul_pow]
      _ ≤ (48 : ℝ≥0∞)^(k*n) := pow_le_pow_left' (by exact_mod_cast ENNReal.ofReal_le_ofReal hcs) _
  have h2 : (2 : ℝ≥0∞)^k ≤ (2 : ℝ≥0∞)^(d*(n+1)) :=
    pow_le_pow_right₀ (by norm_num) (by nlinarith)
  have h48 : (48 : ℝ≥0∞)^(k*n) ≤ (64 : ℝ≥0∞)^(d*(n+1)) :=
    (pow_le_pow_left' (by norm_num : (48:ℝ≥0∞) ≤ 64) _).trans
      (pow_le_pow_right₀ (by norm_num) (by nlinarith))
  have h128 : (128 : ℝ≥0∞)^(d*n) ≤ (128 : ℝ≥0∞)^(d*(n+1)) :=
    pow_le_pow_right₀ (by norm_num) (by nlinarith)
  have hDD : ENNReal.ofReal (D^d)^(n+1) ≤ ENNReal.ofReal (max D 1)^(d*(n+1)) := by
    rw [ENNReal.ofReal_pow hD.le, ← pow_mul]
    exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) _
  calc
    _ = (2 : ℝ≥0∞)^k *
        (unitBallVolume k ^ n * ENNReal.ofReal (Real.sqrt (2*d))^(k*n)) *
        ENNReal.ofReal (D^d)^(n+1) * (128 : ℝ≥0∞)^(d*n) := by ring
    _ ≤ (2 : ℝ≥0∞)^(d*(n+1)) * (64 : ℝ≥0∞)^(d*(n+1)) *
        ENNReal.ofReal (max D 1)^(d*(n+1)) * (128 : ℝ≥0∞)^(d*(n+1)) :=
      mul_le_mul' (mul_le_mul' (mul_le_mul' h2 (hvol.trans h48)) hDD) h128
    _ = ENNReal.ofReal ((16384 * max D 1)^(d*(n+1))) := by
      rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by norm_num)]
      norm_num only [ENNReal.ofReal_ofNat]
      rw [← mul_pow, ← mul_pow, ← mul_pow]
      congr 1
      ring

end ProjectionMoments

end

end OAI
