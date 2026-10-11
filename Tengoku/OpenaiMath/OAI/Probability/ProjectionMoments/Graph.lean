import Tengoku.OpenaiMath.OAI.Probability.GaussianRegression.Main
import Tengoku.OpenaiMath.OAI.Probability.ProjectionMoments.Model

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace ProjectionMoments

lemma volume_preserving_curry (ι κ : Type*) [Fintype ι] [Fintype κ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ ℝ) := by
  apply MeasurePreserving.symm (MeasurableEquiv.curry ι κ ℝ).symm
  refine ⟨(MeasurableEquiv.curry ι κ ℝ).symm.measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [MeasurableEquiv.map_apply]
  have he : (MeasurableEquiv.curry ι κ ℝ).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun i => Set.univ.pi (fun j => s (i,j))) := by
    ext x
    simp [Set.mem_pi, MeasurableEquiv.curry, Function.uncurry]
  rw [he, volume_pi_pi]
  simp_rw [volume_pi_pi]
  exact (Fintype.prod_prod_type (fun p : ι × κ => (volume : Measure ℝ) (s p))).symm

lemma volume_preserving_transpose (m n : ℕ) :
    MeasurePreserving (fun A : Fin m → Fin n → ℝ => fun i j => A j i) := by
  have h1 := (volume_preserving_curry (Fin m) (Fin n)).symm
  have h2 := volume_measurePreserving_piCongrLeft
    (fun _ : Fin n × Fin m => ℝ) (Equiv.prodComm (Fin m) (Fin n))
  have h3 := volume_preserving_curry (Fin n) (Fin m)
  exact h3.comp (h2.comp h1)

section GaussianGraph
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma measurable_vectorSmoothing (ν : Measure E) [SFinite ν] (m : ℕ)
    (φ : (Fin m → ℝ) → ℝ≥0∞) (hφ : Measurable φ) :
    Measurable (vectorSmoothing ν m φ) := by
  apply Measurable.lintegral_prod_right
  exact hφ.comp (by fun_prop)

end GaussianGraph

lemma measurable_ballKernel (m : ℕ) (η : ℝ) : Measurable (ballKernel m η) := by
  exact (measurable_const.indicator Metric.isClosed_closedBall.measurableSet).comp
    (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).measurable

lemma ballKernel_integral (m : ℕ) {η : ℝ} (hη : 0 < η) :
    ∫⁻ y, ballKernel m η y = 1 := by
  have hm : Measurable ((Metric.closedBall (0 : Label m) η).indicator
      (fun _ => (volume (Metric.closedBall (0 : Label m) η))⁻¹)) :=
    measurable_const.indicator Metric.isClosed_closedBall.measurableSet
  change (∫⁻ y, (Metric.closedBall (0 : Label m) η).indicator
    (fun _ => (volume (Metric.closedBall (0 : Label m) η))⁻¹) (WithLp.toLp 2 y)) = 1
  rw [(PiLp.volume_preserving_toLp (Fin m)).lintegral_comp hm,
    lintegral_indicator Metric.isClosed_closedBall.measurableSet]
  simp only [lintegral_const, Measure.restrict_apply_univ]
  apply ENNReal.inv_mul_cancel
  · exact ne_of_gt ((Metric.isOpen_ball.measure_pos volume
      (Metric.nonempty_ball.mpr hη)).trans_le (measure_mono Metric.ball_subset_closedBall))
  · exact (isCompact_closedBall (0 : Label m) η).measure_lt_top.ne

section BallDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] lemma rowMap_apply {m : ℕ} (A : Fin m → E) (t : E) :
    rowMap A t = WithLp.toLp 2 (fun j => ⟪t, A j⟫) := by
  ext j
  simp [rowMap, real_inner_comm]

lemma measurable_ballAverage (ν : Measure E) [SFinite ν] (m : ℕ) (η : ℝ) :
    Measurable (ballAverage ν m η) := by
  exact (measurable_vectorSmoothing ν m (ballKernel m η)
    (measurable_ballKernel m η)).comp
      (measurable_fst.prodMk ((PiLp.continuous_ofLp 2 (fun _ : Fin m => ℝ)).measurable.comp
        measurable_snd))

omit [FiniteDimensional ℝ E] in
lemma ballAverage_eq (ν : Measure E) [SFinite ν] (m : ℕ) (η : ℝ)
    (A : Fin m → E) (y : Label m) :
    ballAverage ν m η (A,y) =
      (ν.map (rowMap A)) (Metric.closedBall y η) /
        volume (Metric.closedBall y η) := by
  have he (t : E) :
      (fun j => WithLp.ofLp y j - ⟪t, A j⟫) = WithLp.ofLp (y - rowMap A t) := by
    simp only [rowMap_apply, WithLp.ofLp_sub]
    rfl
  have hpoint (t : E) :
      ballKernel m η (fun j => WithLp.ofLp y j - ⟪t, A j⟫) =
        (Metric.closedBall y η).indicator
          (fun _ => (volume (Metric.closedBall y η))⁻¹) (rowMap A t) := by
    rw [ballKernel, he, WithLp.toLp_ofLp, Measure.addHaar_closedBall_center volume y]
    have hh : y - rowMap A t ∈ Metric.closedBall (0 : Label m) η ↔
        rowMap A t ∈ Metric.closedBall y η := by
      simp [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
    by_cases h : rowMap A t ∈ Metric.closedBall y η
    · simp only [Set.indicator_of_mem h, Set.indicator_of_mem (hh.mpr h)]
    · simp only [Set.indicator_of_notMem h, Set.indicator_of_notMem (not_congr hh |>.mpr h)]
  simp only [ballAverage, vectorSmoothing, hpoint]
  rw [← lintegral_map (measurable_const.indicator Metric.isClosed_closedBall.measurableSet)
    (rowMap A).continuous.measurable,
    lintegral_indicator Metric.isClosed_closedBall.measurableSet]
  simp [div_eq_mul_inv, mul_comm]

lemma measurable_lowerDensity (ν : Measure E) [SFinite ν] (m : ℕ) :
    Measurable (lowerDensity ν m) :=
  Measurable.liminf (fun _n => measurable_ballAverage ν m _)

theorem lowerDensity_is_density (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ)
    (A : Fin m → E) (hA : ν.map (rowMap A) ≪ (volume : Measure (Label m))) :
    volume.withDensity (fun y => lowerDensity ν m (A,y)) = ν.map (rowMap A) := by
  let ρ := ν.map (rowMap A)
  let v := IsUnifLocDoublingMeasure.vitaliFamily (volume : Measure (Label m)) 1
  have hneg : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Filter.Eventually.of_forall (fun n => ?_)⟩
    · simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · change (0 : ℝ) < ((n : ℝ) + 1)⁻¹
      positivity
  have hae : (fun y => lowerDensity ν m (A,y)) =ᵐ[volume] ρ.rnDeriv volume := by
    filter_upwards [v.ae_tendsto_rnDeriv_of_absolutelyContinuous hA] with y hy
    have ht := IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt volume
      (K := (1 : ℝ)) (x := y) (fun _ : ℕ => y) (fun n => ((n : ℝ) + 1)⁻¹) hneg
      (Filter.Eventually.of_forall (fun n => Metric.mem_closedBall_self (by positivity)))
    have hlim := (hy.comp ht).liminf_eq
    simpa only [lowerDensity, ballAverage_eq, ρ, Function.comp_def] using hlim
  rw [withDensity_congr_ae hae]
  exact Measure.withDensity_rnDeriv_eq _ _ hA

lemma ballAverage_eq_zero_of_far (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ)
    (A : Fin m → E) (z : E) (R η : ℝ) (y : Label m)
    (hsupport : ν.support ⊆ Metric.closedBall z R)
    (hfar : ‖rowMap A‖ * R + η < ‖y - rowMap A z‖) :
    ballAverage ν m η (A,y) = 0 := by
  have hz : (ν.map (rowMap A)) (Metric.closedBall y η) = 0 := by
    rw [Measure.map_apply (rowMap A).continuous.measurable Metric.isClosed_closedBall.measurableSet]
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [ν.support_mem_ae] with t ht hty
    have htR : ‖t-z‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hsupport ht
    have hty' : ‖y - rowMap A t‖ ≤ η := by
      simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hty
    have hn : ‖rowMap A t - rowMap A z‖ ≤ ‖rowMap A‖ * R := by
      rw [← map_sub]
      exact ((rowMap A).le_opNorm _).trans (mul_le_mul_of_nonneg_left htR (norm_nonneg _))
    have hb : ‖y - rowMap A z‖ ≤ η + ‖rowMap A‖ * R := by
      calc
        _ = ‖(y - rowMap A t) + (rowMap A t - rowMap A z)‖ := by congr 1; abel
        _ ≤ ‖y - rowMap A t‖ + ‖rowMap A t - rowMap A z‖ := norm_add_le _ _
        _ ≤ _ := add_le_add hty' hn
    linarith
  simp only [ballAverage_eq, hz, ENNReal.zero_div]

theorem lowerDensity_eq_zero_of_far (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ)
    (A : Fin m → E) (z : E) (R : ℝ) (y : Label m)
    (hsupport : ν.support ⊆ Metric.closedBall z R)
    (hfar : ‖rowMap A‖ * R < ‖y - rowMap A z‖) :
    lowerDensity ν m (A,y) = 0 := by
  have ht : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have he : ∀ᶠ n : ℕ in atTop, ballAverage ν m ((n : ℝ) + 1)⁻¹ (A,y) = 0 := by
    filter_upwards [ht (Iio_mem_nhds (sub_pos.mpr hfar))] with n hn
    apply ballAverage_eq_zero_of_far ν m A z R _ y hsupport
    have hnn : ((n : ℝ) + 1)⁻¹ < ‖y - rowMap A z‖ - ‖rowMap A‖ * R := hn
    linarith
  exact (liminf_congr he).trans (liminf_const _)
end BallDensity

section Rescaling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def rescale (z : E) (R : ℝ) (x : E) : E := R⁻¹ • (x-z)
def dilate (z : E) (R : ℝ) (x : E) : E := R • x + z

omit [FiniteDimensional ℝ E] in
@[fun_prop] lemma measurable_rescale (z : E) (R : ℝ) : Measurable (rescale z R) := by
  unfold rescale; fun_prop
omit [FiniteDimensional ℝ E] in
@[fun_prop] lemma measurable_dilate (z : E) (R : ℝ) : Measurable (dilate z R) := by
  unfold dilate; fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma dilate_rescale (z : E) {R : ℝ} (hR : R ≠ 0) (x : E) :
    dilate z R (rescale z R x) = x := by
  simp [dilate, rescale, smul_smul, hR]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rescale_preimage_closedBall (z b : E) {R : ℝ} (hR : 0 < R) (t : ℝ) :
    rescale z R ⁻¹' Metric.closedBall b t = Metric.closedBall (dilate z R b) (R*t) := by
  ext x
  simp only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
  have he : rescale z R x - b = R⁻¹ • (x - dilate z R b) := by
    simp [rescale, dilate, smul_sub, smul_add, smul_smul, hR.ne', sub_sub, add_comm]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
  rw [inv_mul_le_iff₀ hR]

def normalizedRescale (ν : Measure E) (K a : ℝ) (z : E) (R : ℝ) : Measure E :=
  (ENNReal.ofReal (K * R ^ a))⁻¹ • ν.map (rescale z R)

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma normalizedRescale_finite (ν : Measure E) [IsFiniteMeasure ν]
    (K a : ℝ) (z : E) (R : ℝ) (hKR : 0 < K * R ^ a) :
    IsFiniteMeasure (normalizedRescale ν K a z R) := by
  dsimp [normalizedRescale]
  exact Measure.smul_finite _ (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hKR))

omit [FiniteDimensional ℝ E] in
lemma normalizedRescale_local {ν : Measure E} {K a : ℝ} (hν : AllBallMass ν K a)
    (hK : 0 < K) (z : E) {R : ℝ} (hR : 0 < R) :
    NoiselessRegression.HasLocalMassBound (normalizedRescale ν K a z R) a := by
  intro b _ t ht
  rw [normalizedRescale, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_rescale z R) Metric.isClosed_closedBall.measurableSet,
    rescale_preimage_closedBall z b hR]
  apply (mul_le_mul' le_rfl (hν (dilate z R b) (R*t) (mul_pos hR ht))).trans
  rw [Real.mul_rpow hR.le ht.le, ← mul_assoc,
    ENNReal.ofReal_mul (mul_nonneg hK.le (Real.rpow_nonneg hR.le a)),
    ← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))
      ENNReal.ofReal_ne_top, one_mul]

lemma normalizedRescale_support {ν : Measure E} (K a : ℝ) (z : E) {R : ℝ}
    (hR : 0 < R) (hsupport : ν.support ⊆ Metric.closedBall z R) :
    (normalizedRescale ν K a z R).support ⊆ Metric.closedBall 0 1 := by
  apply Measure.support_subset_of_isClosed Metric.isClosed_closedBall
  apply Measure.smul_absolutelyContinuous.ae_le
  change ∀ᵐ x ∂ν.map (rescale z R), x ∈ Metric.closedBall 0 1
  apply (ae_map_iff (measurable_rescale z R).aemeasurable
    (show MeasurableSet {x : E | x ∈ Metric.closedBall 0 1} from
      Metric.isClosed_closedBall.measurableSet)).mpr
  filter_upwards [ν.support_mem_ae] with x hx
  have he := rescale_preimage_closedBall z (0 : E) hR (1 : ℝ)
  have hx' : x ∈ rescale z R ⁻¹' Metric.closedBall 0 1 := by
    rw [he]
    simpa [dilate] using hsupport hx
  exact hx'

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma ballAverage_smul (ν : Measure E) (c : ℝ≥0∞) (m : ℕ) (η : ℝ)
    (A : Fin m → E) (y : Label m) :
    ballAverage (c • ν) m η (A,y) = c * ballAverage ν m η (A,y) := by
  simp only [ballAverage, vectorSmoothing, lintegral_smul_measure, smul_eq_mul]

lemma ballAverage_dilate (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ)
    (z : E) {R η : ℝ} (hR : 0 < R) (hη : 0 < η) (A : Fin m → E) (b : Label m) :
    ballAverage (ν.map (dilate z R)) m η (A, rowMap A z + b) =
      (ENNReal.ofReal (R ^ m))⁻¹ * ballAverage ν m (η/R) (A, R⁻¹ • b) := by
  rw [ballAverage_eq, ballAverage_eq]
  have hn : ((ν.map (dilate z R)).map (rowMap A)) (Metric.closedBall (rowMap A z + b) η) =
      (ν.map (rowMap A)) (Metric.closedBall (R⁻¹ • b) (η/R)) := by
    rw [Measure.map_apply (rowMap A).continuous.measurable Metric.isClosed_closedBall.measurableSet,
      Measure.map_apply (measurable_dilate z R)
        (Metric.isClosed_closedBall.measurableSet.preimage (rowMap A).continuous.measurable),
      Measure.map_apply (rowMap A).continuous.measurable Metric.isClosed_closedBall.measurableSet]
    congr 1
    ext x
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
    have he : rowMap A (dilate z R x) - (rowMap A z + b) =
        R • (rowMap A x - R⁻¹ • b) := by
      simp only [dilate, map_add, map_smul, smul_sub, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
      abel
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hR, le_div_iff₀ hR, mul_comm]
  have hv : volume (Metric.closedBall (rowMap A z + b) η) =
      ENNReal.ofReal (R ^ m) * volume (Metric.closedBall (R⁻¹ • b) (η/R)) := by
    rw [Measure.addHaar_closedBall volume _ hη.le,
      Measure.addHaar_closedBall volume _ (div_pos hη hR).le,
      finrank_euclideanSpace_fin, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
      ← mul_pow, mul_div_cancel₀ _ hR.ne']
  rw [hn, hv, ENNReal.div_eq_inv_mul, ENNReal.mul_inv
    (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))) (Or.inl ENNReal.ofReal_ne_top)]
  rw [ENNReal.div_eq_inv_mul, mul_assoc]

lemma normalizedRescale_mass {ν : Measure E} {K a : ℝ} (hν : AllBallMass ν K a)
    (hK : 0 < K) (z : E) {R : ℝ} (hR : 0 < R)
    (hsupport : ν.support ⊆ Metric.closedBall z R) :
    normalizedRescale ν K a z R Set.univ ≤ 1 := by
  have he : ν Set.univ = ν (Metric.closedBall z R) := by
    apply measure_congr
    filter_upwards [ν.support_mem_ae] with x hx
    apply propext
    exact iff_of_true (Set.mem_univ x) (hsupport hx)
  rw [normalizedRescale, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_rescale z R) MeasurableSet.univ, Set.preimage_univ, he]
  exact (mul_le_mul' le_rfl (hν z R hR)).trans_eq
    (ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) ENNReal.ofReal_ne_top)

end Rescaling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma vectorSmoothing_pow (ν : Measure E) [IsFiniteMeasure ν]
    (m n : ℕ) (φ : (Fin m → ℝ) → ℝ≥0∞) (hφ : Measurable φ)
    (z : (Fin m → E) × (Fin m → ℝ)) :
    (vectorSmoothing ν m φ z)^(n+1) =
      ∫⁻ w : E × (Fin n → E),
        φ (fun j => z.2 j - ⟪w.1, z.1 j⟫) *
          ∏ i, φ (fun j => z.2 j - ⟪w.2 i, z.1 j⟫)
        ∂ν.prod (Measure.pi (fun _ => ν)) := by
  rw [lintegral_prod _ (by fun_prop)]
  have hG : Measurable (fun v : Fin n → E =>
      ∏ i, φ (fun j => z.2 j - ⟪v i, z.1 j⟫)) := by fun_prop
  simp_rw [lintegral_const_mul _ hG]
  rw [lintegral_mul_const _ (by fun_prop), ← NoiselessRegression.lintegral_pow_pi ν
    (fun t : E => φ (fun j => z.2 j - ⟪t, z.1 j⟫)) (by fun_prop) n]
  exact pow_succ' _ _

end ProjectionMoments
end

end OAI
