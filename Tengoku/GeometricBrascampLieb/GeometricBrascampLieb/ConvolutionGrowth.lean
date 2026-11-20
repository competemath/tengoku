import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.ConvolutionBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # A common continuous quadratic growth coefficient -/

noncomputable section

namespace GeometricBrascampLieb

def convolutionGrowthCoefficient (R t : ℝ) : ℝ :=
  2*(4*t)⁻¹ + 16*((4*t)⁻¹)^2*(1+R^2)

/--
@isnad1 id=le.1h2v.s4.215b3ddc8673 from=translated src=- shape=676e8bff vocab=707117c1
-/
theorem convolutionGrowthCoefficient_nonneg (R : ℝ) {t : ℝ} (ht : 0 < t) :
    0 ≤ convolutionGrowthCoefficient R t := by unfold convolutionGrowthCoefficient; positivity

/--
@isnad1 id=continuo.1h2v.s4.ce5a438949d3 from=translated src=- shape=1b57c06b vocab=251b8dbf
-/
theorem convolutionGrowthCoefficient_continuousAt (R : ℝ) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (convolutionGrowthCoefficient R) t := by
  unfold convolutionGrowthCoefficient
  fun_prop (disch := positivity)

/--
@isnad1 id=le.0h2v.s6.1fcc0eff2f2c from=translated src=- shape=1dbb9b99 vocab=cef4cf1d
-/
theorem shifted_sq_le (r R : ℝ) : (r+R)^2 ≤ 2*(1+R^2)*(1+r^2) := by
  nlinarith [sq_nonneg (r-R), mul_nonneg (sq_nonneg R) (sq_nonneg r)]

/--
@isnad1 id=le.1h3v.s7.4e86e23ecaf4 from=translated src=- shape=9bb102ce vocab=e53373f8
-/
theorem linear_sq_le_convolutionGrowth (r R : ℝ) {t : ℝ} (ht : 0 < t) :
    (2*(4*t)⁻¹*(r+R))^2 ≤ convolutionGrowthCoefficient R t*(1+r^2) := by
  have hb : 0 ≤ (4*t)⁻¹ := by positivity
  have hs := mul_le_mul_of_nonneg_left (shifted_sq_le r R)
    (by positivity : 0 ≤ 4*((4*t)⁻¹)^2)
  have hp : 0 ≤ (2*(4*t)⁻¹+8*((4*t)⁻¹)^2*(1+R^2))*(1+r^2) := by positivity
  dsimp [convolutionGrowthCoefficient]
  nlinarith

/--
@isnad1 id=le.1h3v.s7.cf09c2f0d591 from=translated src=- shape=fa8107b2 vocab=e53373f8
-/
theorem shifted_quadratic_le_convolutionGrowth (r R : ℝ) {t : ℝ} (ht : 0 < t) :
    2*(4*t)⁻¹+8*((4*t)⁻¹)^2*(r+R)^2 ≤ convolutionGrowthCoefficient R t*(1+r^2) := by
  have hb : 0 ≤ (4*t)⁻¹ := by positivity
  have hs := mul_le_mul_of_nonneg_left (shifted_sq_le r R)
    (by positivity : 0 ≤ 8*((4*t)⁻¹)^2)
  have hp : 0 ≤ (4*t)⁻¹*r^2 := mul_nonneg hb (sq_nonneg r)
  dsimp [convolutionGrowthCoefficient]
  nlinarith

open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/--
@isnad1 id=le.5h5v.s8.a3fc734ca9ba from=translated src=- shape=43594cc4 vocab=fc114f98
-/
theorem convolutionLogHeatFlow_gradient_sq_le {f : E → ℝ}
    (hf : Integrable f) (hf0 : ∀ z, 0 ≤ f z) (hmass : 0 < ∫ z, f z) {R : ℝ}
    (hsupport : ∀ z, f z ≠ 0 → ‖z‖ ≤ R) {t : ℝ} (ht : 0 < t) (x : E) :
    ‖(convolutionLogHeatFlow hf hf0 hmass).gradient t x‖^2 ≤
      convolutionGrowthCoefficient R t*(1+‖x‖^2) :=
  (pow_le_pow_left₀ (norm_nonneg _)
    (convolutionLogHeatFlow_gradient_norm_le hf hf0 hmass hsupport ht x) 2).trans
    (linear_sq_le_convolutionGrowth ‖x‖ R ht)

/--
@isnad1 id=le.5h5v.s8.181d8b83b8b1 from=translated src=- shape=caf9ea0e vocab=95a7b5ee
-/
theorem convolutionLogHeatFlow_hessian_le_growth {f : E → ℝ}
    (hf : Integrable f) (hf0 : ∀ z, 0 ≤ f z) (hmass : 0 < ∫ z, f z) {R : ℝ}
    (hsupport : ∀ z, f z ≠ 0 → ‖z‖ ≤ R) {t : ℝ} (ht : 0 < t) (x : E) :
    ‖(convolutionLogHeatFlow hf hf0 hmass).hessian t x‖ ≤
      convolutionGrowthCoefficient R t*(1+‖x‖^2) :=
  (convolutionLogHeatFlow_hessian_norm_le hf hf0 hmass hsupport ht x).trans
    (shifted_quadratic_le_convolutionGrowth ‖x‖ R ht)

end GeometricBrascampLieb
