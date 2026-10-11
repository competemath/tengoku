import Tengoku.OpenaiMath.OAI.Probability.ProjectionMoments.SphereDensity

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
attribute [fun_prop] measurable_ballAverage
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma replicaConstant_real_le [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ν : Measure E} (hν : ν Set.univ ≤ 1) {a : ℝ} {m : ℕ}
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hm : m ≤ Module.finrank ℝ E) :
    NoiselessRegression.replicaConstant ν a m ≤ (128 : ℝ≥0∞)^Module.finrank ℝ E := by
  apply le_trans _ (NoiselessRegression.replicaConstant_le hν hd le_rfl hm)
  have hr : (4 : ℝ)^a ≤ (4 : ℝ)^(Module.finrank ℝ E : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) ha
  have hc : ENNReal.ofReal ((3 : ℝ)^Module.finrank ℝ E * 4^a) ≤
      ENNReal.ofReal ((3 : ℝ)^Module.finrank ℝ E * 4^(Module.finrank ℝ E : ℝ)) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hr (by positivity))
  exact add_le_add le_rfl (mul_le_mul' hc le_rfl)

lemma lintegral_inv_smul_label {m : ℕ} (f : Label m → ℝ≥0∞)
    (hf : Measurable f) {R : ℝ} (hR : 0 < R) :
    ∫⁻ y, f (R⁻¹ • y) = ENNReal.ofReal (R^m) * ∫⁻ y, f y := by
  rw [← lintegral_map hf (by fun_prop), Measure.map_addHaar_smul volume (inv_ne_zero hR.ne'),
    finrank_euclideanSpace_fin, inv_pow, inv_inv, abs_of_nonneg (pow_nonneg hR.le m),
    lintegral_smul_measure, smul_eq_mul]

end

lemma frame_cost_power {d m n : ℕ} (hd : 1 ≤ d) (hm : m ≤ d)
    (a K R : ℝ) (hK : 0 ≤ K) (hR : 0 < R) :
    (2 : ℝ)^m * (Real.sqrt (2*d))^(m*n) *
      ((K*R^(a-m))^(n+1) * R^m * (128 : ℝ)^(d*n)) ≤
      ((256 : ℝ)^d * (256*Real.sqrt d)^((m:ℝ)*(1-1/((n:ℝ)+1))) * K *
        R^(a-(m:ℝ)*(1-1/((n:ℝ)+1))))^(n+1) := by
  have hq : (n : ℝ)+1 ≠ 0 := by positivity
  have hexp : ((m:ℝ)*(1-1/((n:ℝ)+1)))*((n:ℝ)+1) = (m*n:ℕ) := by
    push_cast
    field_simp
    ring
  have hRexp : (a-(m:ℝ)*(1-1/((n:ℝ)+1)))*((n:ℝ)+1) =
      (a-m)*((n:ℝ)+1)+m := by
    field_simp
    ring
  have hscale : (K*R^(a-m))^(n+1)*R^m =
      K^(n+1)*R^((a-(m:ℝ)*(1-1/((n:ℝ)+1)))*((n:ℝ)+1)) := by
    rw [mul_pow, mul_assoc, ← Real.rpow_mul_natCast hR.le,
      ← Real.rpow_natCast R m, ← Real.rpow_add hR]
    congr 2
    rw [Nat.cast_add, Nat.cast_one, hRexp]
  have h2 : (2 : ℝ)^m ≤ 256^d := by
    apply (pow_le_pow_left₀ (by norm_num) (by norm_num : (2 : ℝ) ≤ 256) m).trans
    exact pow_le_pow_right₀ (by norm_num) hm
  have h128 : (128 : ℝ)^(d*n) ≤ 256^(d*n) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) (d*n)
  have hcoef : (2 : ℝ)^m * 128^(d*n) ≤ 256^(d*(n+1)) := by
    apply (mul_le_mul h2 h128 (by positivity) (by positivity)).trans_eq
    rw [← pow_add]
    congr 1
    ring
  have hsqrt : Real.sqrt (2*d) ≤ 256*Real.sqrt d := by
    rw [Real.sqrt_mul (by norm_num)]
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact (Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩)
  have hS : ((256 : ℝ)^d * (256*Real.sqrt d)^((m:ℝ)*(1-1/((n:ℝ)+1))) * K *
      R^(a-(m:ℝ)*(1-1/((n:ℝ)+1))))^(n+1) =
      256^(d*(n+1)) * (256*Real.sqrt d)^(m*n) *
        (K^(n+1)*R^((a-(m:ℝ)*(1-1/((n:ℝ)+1)))*((n:ℝ)+1))) := by
    simp only [mul_pow]
    rw [← pow_mul, ← Real.rpow_mul_natCast (by positivity),
      ← Real.rpow_mul_natCast hR.le]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [hexp, Real.rpow_natCast]
    ring
  rw [hS]
  calc
    _ = (2^m*128^(d*n))*(Real.sqrt (2*d))^(m*n) *
        (K^(n+1)*R^((a-(m:ℝ)*(1-1/((n:ℝ)+1)))*((n:ℝ)+1))) := by
      rw [← hscale]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul hcoef (pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt (m*n))
        (by positivity) (by positivity)) (by positivity)

lemma ennreal_root_bound {q : ℕ} (hq : q ≠ 0) {v : ℝ≥0∞} {B : ℝ}
    (hB : 0 ≤ B) (h : v ≤ ENNReal.ofReal B ^ q) :
    v ^ (1/(q:ℝ)) ≤ ENNReal.ofReal B := by
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hh := ENNReal.rpow_le_rpow h (by positivity : 0 ≤ 1/(q:ℝ))
  rwa [← ENNReal.ofReal_pow hB,
    ENNReal.ofReal_rpow_of_nonneg (pow_nonneg hB q) (by positivity),
    ← Real.rpow_natCast_mul hB, mul_one_div_cancel hq', Real.rpow_one] at hh

lemma frame_cost_root {d m n : ℕ} (hd : 1 ≤ d) (hm : m ≤ d)
    (a K R : ℝ) (hK : 0 ≤ K) (hR : 0 < R) {v : ℝ≥0∞}
    (h : v ≤ (2 : ℝ≥0∞)^m * ENNReal.ofReal (Real.sqrt (2*d))^(m*n) *
      (ENNReal.ofReal (K*R^(a-m))^(n+1) * ENNReal.ofReal (R^m) *
        (128 : ℝ≥0∞)^(d*n))) :
    v ^ (1/((n:ℝ)+1)) ≤
      ENNReal.ofReal ((256 : ℝ)^d * (256*Real.sqrt d)^((m:ℝ)*(1-1/((n:ℝ)+1))) * K *
        R^(a-(m:ℝ)*(1-1/((n:ℝ)+1)))) := by
  have hb := ENNReal.ofReal_le_ofReal (frame_cost_power (n := n) hd hm a K R hK hR)
  simp (discharger := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_pow,
    ENNReal.ofReal_ofNat] at hb
  simp (discharger := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_pow] at h
  have hB : 0 ≤ (256 : ℝ)^d * (256*Real.sqrt d)^((m:ℝ)*(1-1/((n:ℝ)+1))) * K *
      R^(a-(m:ℝ)*(1-1/((n:ℝ)+1))) := by positivity
  have hb' : v ≤ (ENNReal.ofReal ((256 : ℝ)^d *
      (256*Real.sqrt d)^((m:ℝ)*(1-1/((n:ℝ)+1))) * K *
      R^(a-(m:ℝ)*(1-1/((n:ℝ)+1)))))^(n+1) := by
    simp (discharger := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_pow,
      ENNReal.ofReal_ofNat]
    exact h.trans hb
  have hh := ennreal_root_bound (show n+1 ≠ 0 by omega) hB hb'
  simpa only [Nat.cast_add, Nat.cast_one] using hh

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [BorelSpace E] in
lemma measure_eq_zero_of_allBall_zero [BorelSpace E] {ν : Measure E} {a : ℝ}
    (hν : AllBallMass ν 0 a) (z : E) {R : ℝ} (hR : 0 < R)
    (hs : ν.support ⊆ Metric.closedBall z R) : ν = 0 := by
  apply Measure.measure_univ_eq_zero.mp
  have he : ν Set.univ = ν (Metric.closedBall z R) := by
    apply measure_congr
    filter_upwards [ν.support_mem_ae] with x hx
    exact propext (iff_of_true (Set.mem_univ x) (hs hx))
  rw [he]
  apply le_antisymm _ bot_le
  simpa using hν z R hR

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] lemma lowerDensity_zero [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (m : ℕ) (x : (Fin m → E) × Label m) :
    lowerDensity (0 : Measure E) m x = 0 := by
  simp [lowerDensity, ballAverage, vectorSmoothing]

@[simp] lemma coordinateDensity_zero (m : ℕ) (x : (Fin m → E) × (Fin m → ℝ)) :
    coordinateDensity (0 : Measure E) m x = 0 := lowerDensity_zero m _

lemma coordinateDensity_frame_support (ν : Measure E) [IsFiniteMeasure ν] {m : ℕ}
    (z : E) {R : ℝ} (hR : 0 ≤ R) (hs : ν.support ⊆ Metric.closedBall z R)
    (A : Fin m → E) (hA : Orthonormal ℝ A) (y : Fin m → ℝ)
    (hy : R < ‖WithLp.toLp 2 (y-coordinateMap A z)‖) :
    coordinateDensity ν m (A,y) = 0 := by
  apply lowerDensity_eq_zero_of_far ν m A z R (WithLp.toLp 2 y) hs
  have he : WithLp.toLp 2 (y-coordinateMap A z) = WithLp.toLp 2 y - rowMap A z := rfl
  rw [he] at hy
  exact (show ‖rowMap A‖ * R ≤ R from by nlinarith [norm_rowMap_le hA]).trans_lt hy

end ProjectionMoments

end

end OAI
