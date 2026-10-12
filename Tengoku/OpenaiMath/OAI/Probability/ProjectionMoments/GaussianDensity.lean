import Tengoku.OpenaiMath.OAI.Probability.ProjectionMoments.Graph

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma lintegral_gaussianReal_sq :
    ∫⁻ x : ℝ, ENNReal.ofReal (x^2) ∂gaussianReal 0 1 = 1 := by
  have hi : Integrable (fun x : ℝ => x^2) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal' 2 (by norm_num)).integrable_sq
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun x => sq_nonneg x))]
  have hv := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (X := fun x : ℝ => x) (by fun_prop)] at hv
  simpa only [integral_id_gaussianReal, sub_zero, NNReal.coe_one, ENNReal.ofReal_one] using
    congrArg ENNReal.ofReal hv

lemma lintegral_stdGaussian_norm_sq :
    ∫⁻ x : E, ENNReal.ofReal (‖x‖^2) ∂stdGaussian E = Module.finrank ℝ E := by
  let b := stdOrthonormalBasis ℝ E
  rw [stdGaussian_eq_map_pi_orthonormalBasis b, lintegral_map (by fun_prop) (by fun_prop)]
  have he (x : Fin (Module.finrank ℝ E) → ℝ) :
      ‖∑ i, x i • b i‖^2 = ∑ i, (x i)^2 := by
    rw [b.sum_repr_symm (WithLp.toLp 2 x), LinearIsometryEquiv.norm_map]
    exact EuclideanSpace.real_norm_sq_eq _
  simp_rw [he, ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
  rw [lintegral_finsetSum _ (fun i _ => by fun_prop)]
  have hi (i : Fin (Module.finrank ℝ E)) :
      ∫⁻ x : Fin (Module.finrank ℝ E) → ℝ, ENNReal.ofReal (x i ^ 2)
        ∂Measure.pi (fun _ => gaussianReal 0 1) = 1 := by
    rw [← lintegral_gaussianReal_sq]
    exact (measurePreserving_eval (fun _ : Fin (Module.finrank ℝ E) => gaussianReal 0 1) i).lintegral_comp
      (show Measurable (fun x : ℝ => ENNReal.ofReal (x^2)) by fun_prop)
  simp_rw [hi]
  simp

lemma gaussian_norm_ball_mass (hd : 0 < Module.finrank ℝ E) :
    (2 : ℝ≥0∞)⁻¹ ≤ stdGaussian E (Metric.closedBall 0 (Real.sqrt (2 * Module.finrank ℝ E))) := by
  let d : ℝ := Module.finrank ℝ E
  have hd' : 0 < d := by dsimp [d]; exact_mod_cast hd
  have hneg : stdGaussian E {x | ENNReal.ofReal (2*d) ≤ ENNReal.ofReal (‖x‖^2)} ≤ (2 : ℝ≥0∞)⁻¹ := by
    have h := meas_ge_le_lintegral_div (μ := stdGaussian E)
      (f := fun x => ENNReal.ofReal (‖x‖^2)) (by fun_prop)
      (ε := ENNReal.ofReal (2*d)) (by positivity) ENNReal.ofReal_ne_top
    rw [lintegral_stdGaussian_norm_sq] at h
    convert h using 1
    have hd0 : (Module.finrank ℝ E : ℝ≥0∞) ≠ 0 := by exact_mod_cast hd.ne'
    simp only [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat, d,
      ENNReal.ofReal_natCast, div_eq_mul_inv]
    rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), mul_left_comm, ENNReal.mul_inv_cancel hd0 (by simp), mul_one]
  have hsub : (Metric.closedBall (0 : E) (Real.sqrt (2*d)))ᶜ ⊆
      {x | ENNReal.ofReal (2*d) ≤ ENNReal.ofReal (‖x‖^2)} := by
    intro x hx
    have hx' : Real.sqrt (2*d) < ‖x‖ := by simpa only [mem_compl_iff, Metric.mem_closedBall,
      dist_zero_right, not_le] using hx
    apply ENNReal.ofReal_le_ofReal
    have hsq := (sq_le_sq₀ (Real.sqrt_nonneg (2*d)) (norm_nonneg x)).mpr hx'.le
    rwa [Real.sq_sqrt (by positivity)] at hsq
  have hc := (measure_mono hsub).trans hneg
  rw [measure_compl measurableSet_closedBall (measure_ne_top _ _), measure_univ] at hc
  change (2 : ℝ≥0∞)⁻¹ ≤ stdGaussian E (Metric.closedBall 0 (Real.sqrt (2*d)))
  have := tsub_le_iff_left.mp hc
  have he : (1 : ℝ≥0∞) - (2 : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞)⁻¹ := by norm_num
  rw [← he]
  exact tsub_le_iff_right.mpr this

end

lemma map_withDensity_equiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (e : X ≃ᵐ Y) (f : X → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (hs.preimage e.measurable),
    withDensity_apply _ hs, ← lintegral_indicator hs,
    lintegral_map (show Measurable (s.indicator (fun y => f (e.symm y))) from
      (hf.comp e.symm.measurable).indicator hs) e.measurable]
  have he (x : X) : s.indicator (fun y => f (e.symm y)) (e x) =
      (e ⁻¹' s).indicator f x := by
    by_cases hx : e x ∈ s <;> simp [hx]
  simp_rw [he]
  exact (lintegral_indicator (hs.preimage e.measurable) f).symm

lemma density_moment_equiv {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (e : X ≃ᵐ X) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ∞)
    (he : μ.map e = c • μ) {f g : X → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hfg : (μ.withDensity f).map e = μ.withDensity g) (n : ℕ) :
    ∫⁻ y, g y ^ (n+1) ∂μ = c^n * ∫⁻ x, f x ^ (n+1) ∂μ := by
  have hd : g =ᵐ[μ] (fun y => c * f (e.symm y)) := by
    apply (withDensity_eq_iff_of_sigmaFinite hg.aemeasurable (by fun_prop)).mp
    rw [← hfg, map_withDensity_equiv μ e f hf, he, withDensity_smul_measure]
    exact (withDensity_smul c (hf.comp e.symm.measurable)).symm
  have hd' : (fun y => g y ^ (n+1)) =ᵐ[μ]
      (fun y => (c * f (e.symm y)) ^ (n+1)) := by
    filter_upwards [hd] with y hy
    rw [hy]
  rw [lintegral_congr_ae hd']
  simp_rw [mul_pow]
  rw [lintegral_const_mul _ (by fun_prop)]
  have hchange : c * (∫⁻ y, f (e.symm y) ^ (n+1) ∂μ) = ∫⁻ x, f x ^ (n+1) ∂μ := by
    calc
      _ = ∫⁻ y, f (e.symm y) ^ (n+1) ∂(c • μ) := by
        simp only [lintegral_smul_measure, smul_eq_mul]
      _ = _ := by
        rw [← he, lintegral_map_equiv]
        simp
  have hchange' : (∫⁻ y, f (e.symm y) ^ (n+1) ∂μ) =
      c⁻¹ * ∫⁻ x, f x ^ (n+1) ∂μ := by
    rw [← hchange, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]
  rw [hchange', pow_succ, mul_assoc, ← mul_assoc c, ENNReal.mul_inv_cancel hc0 hct,
    one_mul]

end ProjectionMoments

end

end OAI
