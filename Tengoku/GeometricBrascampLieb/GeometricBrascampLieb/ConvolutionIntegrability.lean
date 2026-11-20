import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.ConvolutionGrowth
import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.ConvolutionTails
import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.ConvolutionRegularity
import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.GeometricGrowth
import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.PolynomialHeatBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Heat-integral monotonicity for bounded-support initial data

All analytic conditions are verified for the actual Gaussian regularizations
of nonnegative integrable initial data with positive mass and bounded support.
The two time-endpoint limits and the full measurable BL inequality remain separate.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace GeometricBrascampLieb.Datum

variable {ι E : Type*} {F : ι → Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
  [∀ i, CompleteSpace (F i)]
  [FiniteDimensional ℝ E] [∀ i, FiniteDimensional ℝ (F i)]
  [MeasurableSpace E] [BorelSpace E]
  [∀ i, MeasurableSpace (F i)] [∀ i, BorelSpace (F i)]
  (D : Datum ι E F)

def convolutionAmplitude (f : ∀ i, F i → ℝ) (R : ι → ℝ) (t : ℝ) : ℝ :=
  Real.exp (∑ i, D.weight i*convolutionLogAmplitude (f i) (R i) t)

def convolutionProductGrowth (R : ι → ℝ) (t : ℝ) : ℝ :=
  D.growthCoefficient (fun i => convolutionGrowthCoefficient (R i) t)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem convolutionAmplitude_continuousAt (f : ∀ i, F i → ℝ) (R : ι → ℝ)
    {t : ℝ} (ht : 0 < t) : ContinuousAt (D.convolutionAmplitude f R) t := by
  unfold convolutionAmplitude convolutionLogAmplitude
  fun_prop (disch := positivity)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [∀ i, MeasurableSpace (F i)] [∀ i, BorelSpace (F i)] in
theorem convolutionProductGrowth_continuousAt (R : ι → ℝ) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (D.convolutionProductGrowth R) t := by
  unfold convolutionProductGrowth growthCoefficient convolutionGrowthCoefficient
  fun_prop (disch := positivity)

variable {f : ∀ i, F i → ℝ}
  (hf : ∀ i, Integrable (f i)) (hf0 : ∀ i z, 0 ≤ f i z) (hmass : ∀ i, 0 < ∫ z, f i z)
  {R : ι → ℝ} (hsupport : ∀ i z, f i z ≠ 0 → ‖z‖ ≤ R i)

include hsupport

/-- The five analytic conditions for general bounded-support positive-mass data.-/
theorem convolution_heatIntegrability :
    D.HeatIntegrability (fun i => convolutionLogHeatFlow (hf i) (hf0 i) (hmass i)) := by
  let U := fun i => convolutionLogHeatFlow (hf i) (hf0 i) (hmass i)
  have ha (t : ℝ) (ht : 0 < t) (i : ι) : 0 ≤ convolutionGrowthCoefficient (R i) t :=
    convolutionGrowthCoefficient_nonneg (R i) ht
  have hg (t : ℝ) (ht : 0 < t) (i : ι) (y : F i) :
      ‖(U i).gradient t y‖^2 ≤ convolutionGrowthCoefficient (R i) t*(1+‖y‖^2) :=
    convolutionLogHeatFlow_gradient_sq_le (hf i) (hf0 i) (hmass i) (hsupport i) ht y
  have hh (t : ℝ) (ht : 0 < t) (i : ι) (y : F i) :
      ‖(U i).hessian t y‖ ≤ convolutionGrowthCoefficient (R i) t*(1+‖y‖^2) :=
    convolutionLogHeatFlow_hessian_le_growth (hf i) (hf0 i) (hmass i) (hsupport i) ht y
  apply D.heatIntegrability_of_gaussian_bounds U (D.convolutionAmplitude f R)
    (fun t => (4*t)⁻¹/2) (D.convolutionProductGrowth R)
  · intro t ht
    positivity
  · exact fun t ht => D.growthCoefficient_nonneg (ha t ht)
  · exact fun _ ht => D.convolutionAmplitude_continuousAt f R ht
  · intro t ht
    fun_prop (disch := positivity)
  · exact fun _ ht => D.convolutionProductGrowth_continuousAt R ht
  · exact fun _ ht i => convolutionLogHeatFlow_hessian_continuous (hf i) (hf0 i) (hmass i) ht
  · intro t ht x
    exact D.heatProduct_le_of_logValue_le U t
      (fun i => convolutionLogAmplitude (f i) (R i) t) ((4*t)⁻¹/2)
      (fun i y => convolutionLogHeatFlow_logValue_le (hf i) (hf0 i) (hmass i) (hsupport i) ht y) x
  · exact fun t ht x => D.score_sq_le_of_growth U t (ha t ht) (hg t ht) x
  · exact fun t ht x => D.scoreDerivative_le_of_growth U t (ha t ht) (hh t ht) x
  · exact fun t ht x => D.timeRate_le_of_growth U t (ha t ht) (hg t ht) (hh t ht) x

/-- Monotonicity for actual regularizations, with no unproved analytic hypothesis.-/
theorem convolution_heat_integral_monotoneOn :
    MonotoneOn (fun t => ∫ x, D.heatProduct
      (fun i => convolutionLogHeatFlow (hf i) (hf0 i) (hmass i)) t x) (Ioi 0) :=
  D.heat_integral_monotoneOn _ (D.convolution_heatIntegrability hf hf0 hmass hsupport)

end GeometricBrascampLieb.Datum
