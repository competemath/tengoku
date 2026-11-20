import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.GaussianGeometry
import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.GaussianDomination
import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.Monotonicity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Verified analytic conditions for geometric Gaussian heat flows

All fields of `HeatIntegrability` are proved here for arbitrary centers and
normalizations at a common heat scale.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace GeometricBrascampLieb.Datum

variable {ι E : Type*} {F : ι → Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
  [∀ i, CompleteSpace (F i)]
  [FiniteDimensional ℝ E] [∀ i, FiniteDimensional ℝ (F i)]
  [MeasurableSpace E] [BorelSpace E]
  (D : Datum ι E F)

def gaussianAmplitude (a : ι → ℝ) (z : ∀ i, F i) (t : ℝ) : ℝ :=
  Real.exp ((∑ i, D.weight i * a i) - (Module.finrank ℝ E : ℝ) / 2 * Real.log t -
    (4 * t)⁻¹ * D.gaussianDefect z)

omit [FiniteDimensional ℝ E] [∀ i, FiniteDimensional ℝ (F i)] [MeasurableSpace E] [BorelSpace E] in
/--
@isnad1 id=lt.0h7v.s6.161df2ec9158 from=translated src=- shape=618b98b4 vocab=1f028204
-/
theorem gaussianAmplitude_pos (a : ι → ℝ) (z : ∀ i, F i) (t : ℝ) :
    0 < D.gaussianAmplitude a z t := Real.exp_pos _

omit [FiniteDimensional ℝ E] [∀ i, FiniteDimensional ℝ (F i)] [MeasurableSpace E] [BorelSpace E] in
/--
@isnad1 id=continuo.1h7v.s7.b01b8200f98a from=translated src=- shape=5a663b1e vocab=f63cab87
-/
theorem gaussianAmplitude_continuousAt (a : ι → ℝ) (z : ∀ i, F i) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (D.gaussianAmplitude a z) t := by
  unfold gaussianAmplitude
  fun_prop (disch := positivity)

omit [MeasurableSpace E] [BorelSpace E] in
/--
@isnad1 id=eq.0h8v.s9.5a5ffabb838f from=translated src=- shape=c96fdd8d vocab=9df6e9a8
-/
theorem gaussian_timeDerivative (a : ι → ℝ) (z : ∀ i, F i) (t : ℝ) (x : E) :
    D.heatProduct (fun i => gaussianLogHeatFlow (a i) (z i)) t x *
      D.timeRate (fun i => gaussianLogHeatFlow (a i) (z i)) t x =
    D.gaussianAmplitude a z t *
      (-(2 * t)⁻¹ * (Module.finrank ℝ E : ℝ) + (2 * t)⁻¹ ^ 2 * D.gaussianDefect z +
        (2 * t)⁻¹ ^ 2 * ‖x - D.synthesis z‖ ^ 2) *
      Real.exp (-(4 * t)⁻¹ * ‖x - D.synthesis z‖ ^ 2) := by
  rw [D.gaussian_heatProduct, D.gaussian_timeRate, gaussianAmplitude]
  ring

/--
@isnad1 id=integrab.1h7v.s8.c101f49aadd8 from=translated src=- shape=ed7a22f8 vocab=88f85e3b
-/
theorem gaussian_heatProduct_integrable (a : ι → ℝ) (z : ∀ i, F i) {t : ℝ} (ht : 0 < t) :
    Integrable (D.heatProduct (fun i => gaussianLogHeatFlow (a i) (z i)) t) := by
  change Integrable (fun x => D.heatProduct (fun i => gaussianLogHeatFlow (a i) (z i)) t x)
  simp_rw [D.gaussian_heatProduct]
  exact (integrable_gaussian_shift (D.synthesis z) (by positivity : 0 < (4 * t)⁻¹)).const_mul _

/--
@isnad1 id=integrab.1h7v.s8.27fdd093cf4d from=translated src=- shape=6f4be5bc vocab=3694f9f8
-/
theorem gaussian_timeDerivative_integrable (a : ι → ℝ) (z : ∀ i, F i) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x => D.heatProduct (fun i => gaussianLogHeatFlow (a i) (z i)) t x *
      D.timeRate (fun i => gaussianLogHeatFlow (a i) (z i)) t x) := by
  simp_rw [D.gaussian_timeDerivative]
  exact integrable_quadratic_mul_gaussian (D.synthesis z) _ _ _ (by positivity)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/--
@isnad1 id=eq.1h8v.s8.4ba14fc5d0dc from=translated src=- shape=af003e3b vocab=96563dd0
-/
theorem gaussian_score_norm (a : ι → ℝ) (z : ∀ i, F i) {t : ℝ} (ht : 0 < t) (x : E) :
    ‖D.score (fun i => gaussianLogHeatFlow (a i) (z i)) t x‖ =
      (2 * t)⁻¹ * ‖x - D.synthesis z‖ := by
  rw [D.gaussian_score, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_pos (by positivity : 0 < (2 * t)⁻¹)]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/--
@isnad1 id=le.1h8v.s8.64468a7f0cf8 from=translated src=- shape=ac4bbeb5 vocab=e78359c0
-/
theorem gaussian_scoreDerivative_norm_le (a : ι → ℝ) (z : ∀ i, F i)
    {t : ℝ} (ht : 0 < t) (x : E) :
    ‖D.scoreDerivative (fun i => gaussianLogHeatFlow (a i) (z i)) t x‖ ≤ (2 * t)⁻¹ := by
  rw [D.gaussian_scoreDerivative, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_pos (by positivity : 0 < (2 * t)⁻¹)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)) (by positivity : 0 ≤ (2 * t)⁻¹)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/--
@isnad1 id=le.0h7v.s8.4846fefc55a1 from=translated src=- shape=923968a7 vocab=6a226b81
-/
theorem norm_fluxDerivative_le (U : ∀ i, LogHeatFlow (F i)) (t : ℝ) (x : E) :
    ‖D.fluxDerivative U t x‖ ≤ D.heatProduct U t x *
      (‖D.score U t x‖ ^ 2 + ‖D.scoreDerivative U t x‖) := by
  have h := norm_add_le
    ((D.heatProduct U t x • innerSL ℝ (D.score U t x)).smulRight (D.score U t x))
    (D.heatProduct U t x • D.scoreDerivative U t x)
  simp only [ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (D.heatProduct_pos U t x), innerSL_apply_norm] at h
  calc
    _ ≤ _ := h
    _ = _ := by ring

/--
@isnad1 id=integrab.1h7v.s8.335eeee58bbc from=translated src=- shape=af170d1c vocab=a7796277
-/
theorem gaussian_flux_integrable (a : ι → ℝ) (z : ∀ i, F i) {t : ℝ} (ht : 0 < t) :
    Integrable (D.flux (fun i => gaussianLogHeatFlow (a i) (z i)) t) := by
  let U := fun i => gaussianLogHeatFlow (a i) (z i)
  have hm : AEStronglyMeasurable (D.flux U t) :=
    (continuous_iff_continuousAt.mpr fun x => (D.flux_hasFDerivAt U ht x).continuousAt).aestronglyMeasurable
  apply integrable_of_polynomial_gaussian_bound hm (D.synthesis z) 1
    (D.gaussianAmplitude a z t * (2 * t)⁻¹) (by positivity : 0 < (4 * t)⁻¹)
  intro x
  have h := mul_le_mul_of_nonneg_right
    (show ‖x - D.synthesis z‖ ≤ 1 + ‖x - D.synthesis z‖ by linarith)
    (show 0 ≤ D.gaussianAmplitude a z t * (2 * t)⁻¹ *
      Real.exp (-(4 * t)⁻¹ * ‖x - D.synthesis z‖ ^ 2) by
        exact mul_nonneg (mul_nonneg (D.gaussianAmplitude_pos a z t).le (by positivity)) (Real.exp_pos _).le)
  simp only [flux, norm_smul, Real.norm_eq_abs, abs_of_pos (D.heatProduct_pos U t x)]
  rw [D.gaussian_score_norm a z ht, D.gaussian_heatProduct]
  simpa only [gaussianAmplitude, pow_one, mul_assoc, mul_comm, mul_left_comm] using h

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/--
@isnad1 id=continuo.1h7v.s8.55e18e5b7c73 from=translated src=- shape=d4f84ea7 vocab=95a1b01f
-/
theorem gaussian_fluxDerivative_continuous (a : ι → ℝ) (z : ∀ i, F i) {t : ℝ} (ht : 0 < t) :
    Continuous (D.fluxDerivative (fun i => gaussianLogHeatFlow (a i) (z i)) t) := by
  let U := fun i => gaussianLogHeatFlow (a i) (z i)
  have hQ : Continuous (D.heatProduct U t) :=
    continuous_iff_continuousAt.mpr fun x => (D.heatProduct_hasFDerivAt U ht x).continuousAt
  have hS : Continuous (D.score U t) :=
    continuous_iff_continuousAt.mpr fun x => (D.score_hasFDerivAt U ht x).continuousAt
  have hA : Continuous (D.scoreDerivative U t) := by
    change Continuous (fun x : E => D.scoreDerivative (fun i => gaussianLogHeatFlow (a i) (z i)) t x)
    simp_rw [D.gaussian_scoreDerivative]
    exact continuous_const
  have hT := ((ContinuousLinearMap.smulRightL ℝ E E).continuous.comp
    (hQ.smul ((innerSL ℝ).continuous.comp hS))).clm_apply hS
  exact hT.add (hQ.smul hA)

/--
@isnad1 id=integrab.1h7v.s9.5a561ac47ea6 from=translated src=- shape=216c7cc4 vocab=de9efb2e
-/
theorem gaussian_fluxDerivative_integrable (a : ι → ℝ) (z : ∀ i, F i) {t : ℝ} (ht : 0 < t) :
    Integrable (D.fluxDerivative (fun i => gaussianLogHeatFlow (a i) (z i)) t) := by
  let U := fun i => gaussianLogHeatFlow (a i) (z i)
  let k := (2 * t)⁻¹
  have hk : 0 ≤ k := by dsimp [k]; positivity
  apply integrable_of_polynomial_gaussian_bound
    (D.gaussian_fluxDerivative_continuous a z ht).aestronglyMeasurable (D.synthesis z) 2
    (D.gaussianAmplitude a z t * (k ^ 2 + k)) (by positivity : 0 < (4 * t)⁻¹)
  intro x
  have hp : (k * ‖x - D.synthesis z‖) ^ 2 + k ≤
      (k ^ 2 + k) * (1 + ‖x - D.synthesis z‖ ^ 2) := by
    nlinarith [sq_nonneg k, mul_nonneg hk (sq_nonneg ‖x - D.synthesis z‖)]
  calc
    _ ≤ D.heatProduct U t x * (‖D.score U t x‖ ^ 2 + ‖D.scoreDerivative U t x‖) :=
      D.norm_fluxDerivative_le U t x
    _ ≤ D.heatProduct U t x * ((k * ‖x - D.synthesis z‖) ^ 2 + k) := by
      rw [D.gaussian_score_norm a z ht]
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (D.gaussian_scoreDerivative_norm_le a z ht x)) (D.heatProduct_pos U t x).le
    _ ≤ D.heatProduct U t x * ((k ^ 2 + k) * (1 + ‖x - D.synthesis z‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hp (D.heatProduct_pos U t x).le
    _ = _ := by rw [D.gaussian_heatProduct, gaussianAmplitude]; ring

/-- The analytic hypotheses are now proved for concrete geometric Gaussian flows.
@isnad1 id=heatinte.0h6v.s7.8d8a22238506 from=translated src=- shape=94d85b07 vocab=59000c56
-/
theorem gaussian_heatIntegrability (a : ι → ℝ) (z : ∀ i, F i) :
    D.HeatIntegrability (fun i => gaussianLogHeatFlow (a i) (z i)) where
  product_integrable := fun _ ht => D.gaussian_heatProduct_integrable a z ht
  time_integrable := fun _ ht => D.gaussian_timeDerivative_integrable a z ht
  flux_integrable := fun _ ht => D.gaussian_flux_integrable a z ht
  fluxDerivative_integrable := fun _ ht => D.gaussian_fluxDerivative_integrable a z ht
  local_time_bound := by
    intro t ht
    have h4 : ContinuousAt (fun s : ℝ => (4 * s)⁻¹) t := by fun_prop (disch := positivity)
    have hP : ContinuousAt (fun s : ℝ => -(2 * s)⁻¹ * (Module.finrank ℝ E : ℝ) +
        (2 * s)⁻¹ ^ 2 * D.gaussianDefect z) t := by fun_prop (disch := positivity)
    have hR : ContinuousAt (fun s : ℝ => (2 * s)⁻¹ ^ 2) t := by fun_prop (disch := positivity)
    have h := exists_local_quadratic_gaussian_bound (D.synthesis z) ht
      (by positivity : 0 < (4 * t)⁻¹) (D.gaussianAmplitude_continuousAt a z ht) h4
      hP hR
    simpa only [D.gaussian_timeDerivative] using h

/-- Monotonicity with no unproved heat-integrability hypothesis remaining.
@isnad1 id=monotone.0h6v.s8.8d7fc66ce694 from=translated src=- shape=83dd2567 vocab=3a1fdd15
-/
theorem gaussian_heat_integral_monotoneOn (a : ι → ℝ) (z : ∀ i, F i) :
    MonotoneOn (fun t => ∫ x, D.heatProduct (fun i => gaussianLogHeatFlow (a i) (z i)) t x)
      (Ioi 0) := D.heat_integral_monotoneOn _ (D.gaussian_heatIntegrability a z)

end GeometricBrascampLieb.Datum
