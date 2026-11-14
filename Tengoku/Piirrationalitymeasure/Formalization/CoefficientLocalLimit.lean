import Tengoku.Piirrationalitymeasure.Formalization.CoefficientGaussian
import Tengoku.Piirrationalitymeasure.Formalization.GlobalGaussianBound
import Tengoku.Piirrationalitymeasure.Formalization.GaussianIntegralLimit
import Tengoku.Piirrationalitymeasure.Formalization.LatticeFourierInversion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The actual single-lattice-point Gaussian asymptotic used in Section 4.1. -/

namespace PiIrrationality

open MeasureTheory Filter
open scoped Topology

theorem coefficientCentered_integral {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (q : ℕ) (hm : coefficientMean x = (q : ℝ)) (n : ℕ) :
    (∫ t in -Real.pi..Real.pi, coefficientCenteredChar x t ^ n) =
      (2 * Real.pi : ℂ) * (coefficientProbability x n (q * n) : ℂ) := by
  have h := lattice_fourier_inversion (coefficientLaw x hx0 hx1 n) (q * n)
  simp_rw [coefficientLaw_charFun hx0 hx1, coefficientLaw_toReal] at h
  have he (t : ℝ) : coefficientCenteredChar x t ^ n =
      coefficientChar x t ^ n * Complex.exp (-((q * n : ℕ) : ℂ) * (t : ℂ) * Complex.I) := by
    simp only [coefficientCenteredChar, mul_pow, ← Complex.exp_nat_mul, hm,
      Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_natCast, Nat.cast_mul]
    congr 1
    congr 1
    ring
  simpa only [← he] using h

theorem gaussian_normalization (v : ℝ) :
    Real.sqrt (2 * Real.pi / v) / (2 * Real.pi) = 1 / Real.sqrt (2 * Real.pi * v) := by
  have hπ : 0 ≤ 2 * Real.pi := by positivity
  calc
    Real.sqrt (2 * Real.pi / v) / (2 * Real.pi) =
        (Real.sqrt (2 * Real.pi) / (2 * Real.pi)) / Real.sqrt v := by
      rw [Real.sqrt_div hπ]
      ring
    _ = (1 / Real.sqrt (2 * Real.pi)) / Real.sqrt v := by rw [Real.sqrt_div_self']
    _ = _ := by rw [Real.sqrt_mul hπ]; ring

end PiIrrationality
