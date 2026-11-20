import Tengoku.Seed.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Tengoku.Seed.MeasureTheory.Group.Integral
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Polynomial Gaussian bounds

All natural moments of an isotropic Gaussian are integrable in a
finite-dimensional real inner product space, including dimension zero.
-/

noncomputable section
open MeasureTheory

namespace GeometricBrascampLieb

/--
@isnad1 id=le.1h3v.s7.b5c3df71b12f from=translated src=- shape=2aae1c1a vocab=e5051a80
-/
theorem even_pow_mul_gaussian_le (r : ℝ) (n : ℕ) {b : ℝ} (hb : 0 < b) :
    (r ^ 2) ^ n * Real.exp (-b * r ^ 2) ≤
      ((n.factorial : ℝ) / (b / 2) ^ n) * Real.exp (-(b / 2) * r ^ 2) := by
  have hc : 0 < b / 2 := half_pos hb
  have hf : 0 < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hp := (div_le_iff₀ hf).mp
    (Real.pow_div_factorial_le_exp ((b / 2) * r ^ 2) (mul_nonneg hc.le (sq_nonneg r)) n)
  rw [mul_pow] at hp
  have hp' : (r ^ 2) ^ n ≤ ((n.factorial : ℝ) / (b / 2) ^ n) *
      Real.exp ((b / 2) * r ^ 2) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (pow_pos hc n)).mpr
    simpa only [mul_comm] using hp
  calc
    _ ≤ (((n.factorial : ℝ) / (b / 2) ^ n) * Real.exp ((b / 2) * r ^ 2)) *
        Real.exp (-b * r ^ 2) := mul_le_mul_of_nonneg_right hp' (Real.exp_pos _).le
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/--
@isnad1 id=integrab.1h2v.s7.68772bb5c081 from=translated src=- shape=ea241769 vocab=462c16eb
-/
theorem integrable_gaussian {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : E => Real.exp (-b * ‖x‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := E) (b := (b : ℂ)) (by simpa using hb) 0 0).re
  change Integrable (fun x : E => (Complex.exp (-(b : ℂ) * ‖x‖ ^ 2 + 0 * inner ℝ 0 x)).re) at h
  simpa only [zero_mul, add_zero, ← Complex.ofReal_pow, ← Complex.ofReal_neg,
    ← Complex.ofReal_mul, ← Complex.ofReal_exp, Complex.ofReal_re] using h

/--
@isnad1 id=integrab.1h3v.s7.7452fb2cec4c from=translated src=- shape=af756803 vocab=462c16eb
-/
theorem integrable_even_norm_pow_mul_gaussian (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : E => (‖x‖ ^ 2) ^ n * Real.exp (-b * ‖x‖ ^ 2)) := by
  apply ((integrable_gaussian (E := E) (half_pos hb)).const_mul
    ((n.factorial : ℝ) / (b / 2) ^ n)).mono' (by fun_prop)
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact even_pow_mul_gaussian_le ‖x‖ n hb

/-- Every natural polynomial moment has a Gaussian integrable majorant.
@isnad1 id=integrab.1h3v.s7.bcb1a4b083b2 from=translated src=- shape=0ea71d7a vocab=462c16eb
-/
theorem integrable_norm_pow_mul_gaussian (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : E => ‖x‖ ^ n * Real.exp (-b * ‖x‖ ^ 2)) := by
  apply ((integrable_gaussian (E := E) hb).add
    (integrable_even_norm_pow_mul_gaussian (E := E) n hb)).mono' (by fun_prop)
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hp : ‖x‖ ^ n ≤ 1 + (‖x‖ ^ 2) ^ n := by
      rw [← pow_mul, mul_comm 2 n, pow_mul]
      nlinarith [sq_nonneg (‖x‖ ^ n - 1)]
    simpa only [Pi.add_apply, add_mul, one_mul] using
      mul_le_mul_of_nonneg_right hp (Real.exp_pos (-b * ‖x‖ ^ 2)).le

/--
@isnad1 id=integrab.1h4v.s7.1dbc980e0fcb from=translated src=- shape=cba0c3fc vocab=e32d20bb
-/
theorem integrable_norm_sub_pow_mul_gaussian (z : E) (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : E => ‖x - z‖ ^ n * Real.exp (-b * ‖x - z‖ ^ 2)) := by
  simpa only [sub_eq_add_neg] using
    (integrable_norm_pow_mul_gaussian (E := E) n hb).comp_add_right (-z)

/--
@isnad1 id=integrab.1h3v.s7.29040be8004a from=translated src=- shape=7b5f031e vocab=e32d20bb
-/
theorem integrable_gaussian_shift (z : E) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : E => Real.exp (-b * ‖x - z‖ ^ 2)) := by
  simpa only [pow_zero, one_mul] using integrable_norm_sub_pow_mul_gaussian z 0 hb

/-- Useful for scalar, vector, and operator-valued derivatives of a Gaussian.
@isnad1 id=integrab.3h7v.s8.ea2ebb839342 from=translated src=- shape=7b8ccaba vocab=863556dc
-/
theorem integrable_of_polynomial_gaussian_bound
    {G : Type*} [NormedAddCommGroup G] {f : E → G}
    (hf : AEStronglyMeasurable f) (z : E) (n : ℕ) (C : ℝ) {b : ℝ} (hb : 0 < b)
    (hbound : ∀ x, ‖f x‖ ≤ C * (1 + ‖x - z‖ ^ n) * Real.exp (-b * ‖x - z‖ ^ 2)) :
    Integrable f := by
  have hi := ((integrable_gaussian_shift z hb).add
    (integrable_norm_sub_pow_mul_gaussian z n hb)).const_mul C
  apply hi.mono' hf
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Pi.add_apply, add_mul, mul_add, one_mul, mul_one, mul_assoc] using hbound x

end GeometricBrascampLieb
