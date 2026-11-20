import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.ScalarTargets
import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.MeasurableInequality
import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.Complex

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Real and complex scalar-target Brascamp–Lieb

These interfaces use the norm-one and quadratic-frame hypotheses supplied by
projection-density applications. In the complex case the underlying real
inner product and its canonical volume are retained. The complex exponents
remain `c i`, since the real target dimension is two.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace GeometricBrascampLieb

section Real
variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Real scalar targets, stated using a quadratic frame identity.
@isnad1 id=le.4h5v.s9.e8720710c34c from=translated src=- shape=82bd7671 vocab=73b88682
-/
theorem real_lintegral_prod_le_of_norm_sq
    (B : ι → (E →L[ℝ] ℝ)) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hB : ∀ i, ‖B i‖ = 1)
    (hframe : ∀ x, ∑ i, c i * ‖B i x‖ ^ 2 = ‖x‖ ^ 2)
    (f : ι → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i, (f i (B i x)) ^ c i) ≤ ∏ i, (∫⁻ y, f i y) ^ c i :=
  (Datum.ofNormSq B c hc (fun i => scalar_coisometry_of_norm_one (B i) (hB i))
    hframe).lintegral_prod_le f hf

end Real

section Complex
variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [InnerProductSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Complex scalar targets with their ordinary two-dimensional Lebesgue measure.
@isnad1 id=le.4h5v.s9.3a3a068ca484 from=translated src=- shape=b427ea89 vocab=043bddec
-/
theorem complex_lintegral_prod_le_of_norm_sq
    (B : ι → (E →L[ℂ] ℂ)) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hB : ∀ i, ‖B i‖ = 1)
    (hframe : ∀ x, ∑ i, c i * ‖B i x‖ ^ 2 = ‖x‖ ^ 2)
    (f : ι → ℂ → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i, (f i (B i x)) ^ c i) ≤ ∏ i, (∫⁻ y, f i y) ^ c i :=
  (Datum.ofNormSq (fun i => (B i).restrictScalars ℝ) c hc
    (fun i => coisometry_restrictScalars (B i)
      (scalar_coisometry_of_norm_one (B i) (hB i))) hframe).lintegral_prod_le f hf

end Complex
end GeometricBrascampLieb
