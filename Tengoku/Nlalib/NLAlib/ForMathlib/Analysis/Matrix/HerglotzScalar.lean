import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.Matrix.QuadraticPositiveMap
import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.Complex.Harmonic.StieltjesCharacterization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Actual scalar measures for matrix Herglotz probes

Holomorphy, positive matrix imaginary part, matrix normalization at infinity,
and an exterior imaginary bound construct each scalar quadratic Stieltjes
measure. No scalar representing measure is supplied to the theorem.
-/

noncomputable section
open Matrix MeasureTheory Filter Set
open scoped Topology Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule
namespace Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The nonnegative normalization mass of a quadratic matrix probe.-/
def quadraticProbeMass (v : n → ℂ) : NNReal :=
  ⟨matrixRealQuadraticFormCLM v 1, by
    change 0 ≤ (star v ⬝ᵥ (1 *ᵥ v)).re
    rw [one_mulVec]
    exact (RCLike.nonneg_iff.mp (dotProduct_star_self_nonneg v)).1⟩

/-- Probe mass is exactly the identity quadratic form.-/
theorem ofReal_quadraticProbeMass (v : n → ℂ) :
    ((quadraticProbeMass v : ℝ) : ℂ) = matrixQuadraticFormCLM v 1 := by
  apply Complex.ext
  · rfl
  · have hI : (1 : Matrix n n ℂ).IsHermitian := isHermitian_one
    exact (hI.im_star_dotProduct_mulVec_self v).symm

/-- Matrix normalization transports through each continuous quadratic probe.-/
theorem tendsto_mul_I_matrixQuadraticFormCLM
    (M : ℂ → Matrix n n ℂ)
    (hlim : Tendsto (fun y : ℝ => ((y : ℂ) * Complex.I) • M ((y : ℂ) * Complex.I))
      atTop (𝓝 (-1))) (v : n → ℂ) :
    Tendsto (fun y : ℝ => (y : ℂ) * Complex.I * matrixQuadraticFormCLM v (M ((y : ℂ) * Complex.I)))
      atTop (𝓝 (-(quadraticProbeMass v : ℝ) : ℂ)) := by
  have h := ((matrixQuadraticFormCLM v).continuous.tendsto (-1)).comp hlim
  simpa only [Function.comp_def, map_smul, smul_eq_mul, map_neg,
    ← ofReal_quadraticProbeMass, Complex.ofReal_neg] using h

/-- Matrix exterior imaginary bounds transport to scalar probes with
the exact same exterior radius.-/
theorem im_matrixQuadraticFormCLM_le_mul_of_norm
    (M : ℂ → Matrix n n ℂ) (v : n → ℂ) (a C : ℝ)
    (hb : ∀ z : ℂ, 0 < z.im → a ≤ |z.re| →
      ‖(imaginaryPart (M z) : Matrix n n ℂ)‖ ≤ C * z.im) :
    ∀ z : ℂ, 0 < z.im → a ≤ |z.re| →
      (matrixQuadraticFormCLM v (M z)).im ≤ (‖matrixRealQuadraticFormCLM v‖ * C) * z.im := by
  intro z hz hza
  rw [im_matrixQuadraticFormCLM]
  calc
    _ ≤ ‖matrixRealQuadraticFormCLM v (imaginaryPart (M z) : Matrix n n ℂ)‖ :=
      le_abs_self _
    _ ≤ ‖matrixRealQuadraticFormCLM v‖ * ‖(imaginaryPart (M z) : Matrix n n ℂ)‖ :=
      (matrixRealQuadraticFormCLM v).le_opNorm _
    _ ≤ ‖matrixRealQuadraticFormCLM v‖ * (C * z.im) :=
      mul_le_mul_of_nonneg_left (hb z hz hza) (norm_nonneg _)
    _ = _ := (mul_assoc _ _ _).symm

end Matrix
