import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.HeatScaling
import Tengoku.Seed.Analysis.Real.Sqrt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The large-time endpoint and the BL bound at every positive heat time

For nonnegative integrable inputs with positive mass and bounded support, the
heat-product integral converges to the product of masses. Together with the
proved monotonicity this gives the sharp bound for every positive-time
regularization. Passing to the original measurable inputs remains separate.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GeometricBrascampLieb.Datum

variable {ι E : Type*} {F : ι → Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
  [∀ i, CompleteSpace (F i)]
  [FiniteDimensional ℝ E] [∀ i, FiniteDimensional ℝ (F i)]
  [MeasurableSpace E] [BorelSpace E]
  [∀ i, MeasurableSpace (F i)] [∀ i, BorelSpace (F i)]
  (D : Datum ι E F) {f : ∀ i, F i → ℝ}
  (hf : ∀ i, Integrable (f i)) (hf0 : ∀ i z, 0 ≤ f i z) (hmass : ∀ i, 0 < ∫ z, f i z)
  {R : ι → ℝ} (hsupport : ∀ i z, f i z ≠ 0 → ‖z‖ ≤ R i)

include hf hf0 hmass hsupport

/--
@isnad1 id=tendsto.4h6v.s9.3675c6aaa6bc from=translated src=- shape=de199d36 vocab=7c1260bb
-/
theorem integral_prod_heatConvolution_tendsto_sq_atTop :
    Tendsto (fun a : ℝ => ∫ x, ∏ i, (heatConvolution (f i) (a^2) (D.map i x))^D.weight i)
      atTop (𝓝 (∏ i, (∫ z, f i z)^D.weight i)) := by
  have h := (D.tendsto_integral_rescaledProduct_zero hf hf0 hmass hsupport).comp
    (tendsto_inv_atTop_zero : Tendsto (fun a : ℝ => a⁻¹) atTop (𝓝 0))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  exact (D.integral_prod_heatConvolution_eq_rescaled hf hf0 hmass ha).symm

/-- The actual large-time endpoint, in the original heat parameter.
@isnad1 id=tendsto.4h6v.s9.466a8b04921d from=translated src=- shape=5a1ed120 vocab=3c639bdb
-/
theorem integral_prod_heatConvolution_tendsto_atTop :
    Tendsto (fun t => ∫ x, ∏ i, (heatConvolution (f i) t (D.map i x))^D.weight i)
      atTop (𝓝 (∏ i, (∫ z, f i z)^D.weight i)) := by
  have h := (D.integral_prod_heatConvolution_tendsto_sq_atTop hf hf0 hmass hsupport).comp
    Real.tendsto_sqrt_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  change (∫ x, ∏ i, (heatConvolution (f i) ((Real.sqrt t)^2) (D.map i x))^D.weight i) = _
  rw [Real.sq_sqrt ht]

/-- The sharp geometric BL bound for every positive heat regularization.
@isnad1 id=le.5h7v.s9.db20013c3e07 from=translated src=- shape=dbe6422b vocab=1fc6148a
-/
theorem integral_prod_heatConvolution_le {t : ℝ} (ht : 0 < t) :
    (∫ x, ∏ i, (heatConvolution (f i) t (D.map i x))^D.weight i) ≤
      ∏ i, (∫ z, f i z)^D.weight i := by
  apply ge_of_tendsto (D.integral_prod_heatConvolution_tendsto_atTop hf hf0 hmass hsupport)
  filter_upwards [eventually_ge_atTop t] with s hs
  exact D.integral_prod_heatConvolution_monotoneOn hf hf0 hmass hsupport ht (ht.trans_le hs) hs

end GeometricBrascampLieb.Datum
