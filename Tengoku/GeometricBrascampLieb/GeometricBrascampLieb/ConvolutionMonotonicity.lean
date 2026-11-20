import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.ConvolutionIntegrability

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The heat monotonicity theorem in the usual product notation -/

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
  (D : Datum ι E F) {f : ∀ i, F i → ℝ}
  (hf : ∀ i, Integrable (f i)) (hf0 : ∀ i z, 0 ≤ f i z) (hmass : ∀ i, 0 < ∫ z, f i z)

include hf hf0 hmass

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem heatProduct_convolution_eq_prod {t : ℝ} (ht : 0 < t) (x : E) :
    D.heatProduct (fun i => convolutionLogHeatFlow (hf i) (hf0 i) (hmass i)) t x =
      ∏ i, (heatConvolution (f i) t (D.map i x)) ^ D.weight i := by
  rw [heatProduct, logProduct, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  change Real.exp (D.weight i*Real.log (heatConvolution (f i) t (D.map i x))) = _
  rw [Real.rpow_def_of_pos (heatConvolution_pos (hf i) (hf0 i) (hmass i) ht _)]
  congr 1
  ring

/-- The usual BL heat functional is nondecreasing for bounded-support data.-/
theorem integral_prod_heatConvolution_monotoneOn {R : ι → ℝ}
    (hsupport : ∀ i z, f i z ≠ 0 → ‖z‖ ≤ R i) :
    MonotoneOn (fun t => ∫ x, ∏ i, (heatConvolution (f i) t (D.map i x)) ^ D.weight i) (Ioi 0) := by
  intro t ht s hs hts
  have h := D.convolution_heat_integral_monotoneOn hf hf0 hmass hsupport ht hs hts
  have he (r : ℝ) (hr : 0 < r) :
      (fun x => D.heatProduct (fun i => convolutionLogHeatFlow (hf i) (hf0 i) (hmass i)) r x) =
        (fun x => ∏ i, (heatConvolution (f i) r (D.map i x)) ^ D.weight i) :=
    funext (D.heatProduct_convolution_eq_prod hf hf0 hmass hr)
  change (∫ x, D.heatProduct (fun i => convolutionLogHeatFlow (hf i) (hf0 i) (hmass i)) t x) ≤
    (∫ x, D.heatProduct (fun i => convolutionLogHeatFlow (hf i) (hf0 i) (hmass i)) s x) at h
  rw [he t ht, he s hs] at h
  exact h

end GeometricBrascampLieb.Datum
