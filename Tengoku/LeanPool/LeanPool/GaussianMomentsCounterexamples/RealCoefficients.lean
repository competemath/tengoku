/-
Copyright (c) 2026 long-mathematics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher D. Long
-/
module

public import Tengoku.LeanPool.LeanPool.GaussianMomentsCounterexamples.GaussianMeasure
public import Tengoku

/-! A real-coefficient polynomial whose Gaussian second moment vanishes is zero. -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory MvPolynomial
namespace GaussianMomentsCounterexamples

/--
@isnad1 id=isopenpo.0h0v.s4.58a8ad13b1f6 from=translated src=- shape=c6bef40b vocab=ac884766
-/
instance standardGaussian_isOpenPosMeasure : Measure.IsOpenPosMeasure (gaussianReal 0 1) :=
  (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : NNReal) ≠ 0)).isOpenPosMeasure

/--
@isnad1 id=isopenpo.0h1v.s5.69a848555e52 from=translated src=- shape=e72d7878 vocab=eaa14dd7
-/
instance gaussianMeasure_isOpenPosMeasure (n : ℕ) :
  Measure.IsOpenPosMeasure (gaussianMeasure n) := by
  unfold gaussianMeasure
  infer_instance

/--
@isnad1 id=eq.0h3v.s7.5d2becaaa8ba from=translated src=- shape=6a77a107 vocab=d4945c36
-/
lemma realEval_map_real {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    realEval (map Complex.ofRealHom P) x = (eval x P : ℂ) := by
  exact (MvPolynomial.map_eval Complex.ofRealHom x P).symm

/--
@isnad1 id=integrab.0h2v.s7.e286b36145eb from=translated src=- shape=e794b079 vocab=78baa87e
-/
lemma integrable_real_polynomial {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    Integrable (fun x => eval x P) (gaussianMeasure n) := by
  have h := (integrable_realEval (map Complex.ofRealHom P)).re
  change Integrable (fun x => Complex.re (realEval (map Complex.ofRealHom P) x)) _ at h
  simpa only [realEval_map_real, Complex.ofReal_re] using h

/-- Nonnegative Gaussian second moment detects every nonzero real polynomial.
@isnad1 id=eq.1h2v.s7.a2b338232be5 from=translated src=- shape=6029a516 vocab=7390c0d1
-/
theorem real_polynomial_eq_zero_of_second_moment {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (h : ∫ x, (eval x P) ^ 2 ∂gaussianMeasure n = 0) : P = 0 := by
  have hint : Integrable (fun x => (eval x P) ^ 2) (gaussianMeasure n) := by
    convert integrable_real_polynomial (P ^ 2) using 1
    funext x
    exact (map_pow (eval x) P 2).symm
  have hae : (fun x => (eval x P) ^ 2) =ᵐ[gaussianMeasure n] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (eval x P)) hint).mp h
  have hae' : (fun x => eval x P) =ᵐ[gaussianMeasure n] 0 := by
    filter_upwards [hae] with x hx
    exact sq_eq_zero_iff.mp hx
  have heq := (gaussianMeasure n).eq_of_ae_eq hae' P.continuous_eval continuous_zero
  apply MvPolynomial.funext
  intro x
  change eval x P = 0
  exact congrFun heq x

/-- Casting real coefficients commutes with the genuine Gaussian expectation.
@isnad1 id=eq.0h2v.s7.29adaec3c79a from=translated src=- shape=74c2d6c1 vocab=d25461c5
-/
theorem expectation_map_real {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    expectation (map Complex.ofRealHom P) =
      ((∫ x, eval x P ∂gaussianMeasure n : ℝ) : ℂ) := by
  unfold expectation
  simp_rw [realEval_map_real]
  exact integral_complex_ofReal

/-- The second-moment obstruction in the manuscript's complex-valued expectation interface.
@isnad1 id=eq.1h2v.s7.049b438ce277 from=translated src=- shape=42133ec0 vocab=0860c726
-/
theorem real_polynomial_eq_zero_of_complex_second_moment {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ)
    (h : expectation ((map Complex.ofRealHom P) ^ 2) = 0) : P = 0 := by
  apply real_polynomial_eq_zero_of_second_moment P
  rw [← map_pow, expectation_map_real] at h
  have hr : (∫ x, eval x (P ^ 2) ∂gaussianMeasure n) = 0 := Complex.ofReal_eq_zero.mp h
  convert hr using 1
  congr 1
  funext x
  exact (map_pow (eval x) P 2).symm

/-- Consequently a real-coefficient polynomial with all positive Gaussian moments zero is zero.
@isnad1 id=eq.1h2v.s8.a07462a03fc7 from=translated src=- shape=25fcdbc8 vocab=fb2b54a3
-/
theorem real_polynomial_eq_zero_of_all_moments {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (h : ∀ m : ℕ, 1 ≤ m → expectation ((map Complex.ofRealHom P) ^ m) = 0) : P = 0 :=
  real_polynomial_eq_zero_of_complex_second_moment P (h 2 (by decide))

end GaussianMomentsCounterexamples
