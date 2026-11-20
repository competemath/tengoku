import Tengoku.PshdLean.PshLines.PSHD.FourierProjection
import Tengoku.Seed.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Gaussian duality for finite measures

A Gaussian regularization identity for the Fourier-energy argument in
`pshd-vibe`, Lemma 1.4. Both Fourier duality and the Gaussian integral are
reused from mathlib.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace FourierTransform

namespace PshLines.PSHD

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [BorelSpace E] in
/-- The measure transform is the vector Fourier integral of the constant one.-/
theorem measureFourier_eq_vectorFourier (μ : Measure E) (ξ : E) :
    measureFourier μ ξ =
      VectorFourier.fourierIntegral Real.fourierChar μ (innerₗ E) (fun _ ↦ (1 : ℂ)) ξ := by
  rw [measureFourier_eq_integral, Real.vector_fourierIntegral_eq_integral_exp_smul]
  simp

variable [FiniteDimensional ℝ E]

/-- Gaussian testing of a finite measure's transform equals testing the measure
against the Fourier-transformed Gaussian.-/
theorem integral_measureFourier_mul_gaussian (μ : Measure E) [IsFiniteMeasure μ]
    {b : ℂ} (hb : 0 < b.re) :
    (∫ ξ : E, measureFourier μ ξ * Complex.exp (-b * ‖ξ‖ ^ 2)) =
      ∫ x, (Real.pi / b) ^ (Module.finrank ℝ E / 2 : ℂ) *
        Complex.exp (-Real.pi ^ 2 * ‖x‖ ^ 2 / b) ∂μ := by
  have hg : Integrable (fun ξ : E ↦ Complex.exp (-b * ‖ξ‖ ^ 2)) := by
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb 0 (0 : E)
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (μ := μ) (ν := volume) (L := innerₗ E) (f := fun _ ↦ (1 : ℂ))
    (g := fun ξ : E ↦ Complex.exp (-b * ‖ξ‖ ^ 2))
    Real.continuous_fourierChar (by simpa using continuous_inner) (integrable_const 1) hg
  simp only [← measureFourier_eq_vectorFourier, smul_eq_mul, flip_innerₗ, one_mul] at h
  rw [h]
  congr 1
  funext x
  exact fourier_gaussian_innerProductSpace hb x

end PshLines.PSHD
