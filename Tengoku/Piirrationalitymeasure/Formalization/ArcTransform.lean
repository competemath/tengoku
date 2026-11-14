import Tengoku.Piirrationalitymeasure.Formalization.ArcPhase
import Tengoku.Piirrationalitymeasure.Formalization.Statements

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The degree-six transformed numerator for arbitrary real phase parameters. -/

namespace PiIrrationality

open Polynomial
open scoped ContDiff

noncomputable def transformedArcD (e : ℝ) : Polynomial ℝ :=
  C (1 + e ^ 2) + C 2 * X + X ^ 2

noncomputable def transformedArcH (e : ℝ) : Polynomial ℝ :=
  C (625 * (1 + e ^ 2)) + C (400 * (4 - 3 * e)) * X + C 1600 * X ^ 2

noncomputable def transformedArcJ (e : ℝ) : Polynomial ℝ :=
  C (625 * (1 + e ^ 2)) + C (200 * e + 1400) * X + C 800 * X ^ 2

noncomputable def parameterPhasePolynomial (p : ℝ × ℝ) (e : ℝ) : Polynomial ℝ :=
  C (2 * p.1) * transformedArcD e * transformedArcH e * transformedArcJ e +
    C p.2 * X * transformedArcD e * transformedArcJ e *
      (C (400 * (4 - 3 * e)) + C 3200 * X) -
    X * transformedArcD e * transformedArcH e * (C (200 * e + 1400) + C 1600 * X) +
    C (1 - p.1 - 2 * p.2) * X * transformedArcH e * transformedArcJ e * (C 2 + C 2 * X)

theorem parameterPhasePolynomial_degree_le (p : ℝ × ℝ) (e : ℝ) :
    (parameterPhasePolynomial p e).natDegree ≤ 6 := by
  unfold parameterPhasePolynomial transformedArcD transformedArcH transformedArcJ
  compute_degree!

set_option maxHeartbeats 0 in
-- Normalize the multivariate rational identity after clearing all denominators.
theorem parameterPhasePolynomial_transformed (p : ℝ × ℝ) (e u : ℝ) (hu : 1 + u ≠ 0) :
    (1 + u) ^ 6 * arcClearedDerivative p.1 p.2 e (u / (1 + u)) =
      (1 + e ^ 2) * (parameterPhasePolynomial p e).eval u := by
  simp only [parameterPhasePolynomial, transformedArcD, transformedArcH, transformedArcJ,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  unfold arcClearedDerivative arcD arcH arcJ arcDderiv arcHderiv arcJderiv
  field_simp [hu]
  ring

set_option maxHeartbeats 0 in
-- Compare the two explicit degree-six formulas by polynomial normalization.
theorem parameterPhasePolynomial_candidate (e : ℝ) :
    parameterPhasePolynomial candidate e = C ((125 : ℝ) / 557) * phaseTransformedPolynomial e := by
  apply Polynomial.funext
  intro u
  simp only [parameterPhasePolynomial, transformedArcD, transformedArcH, transformedArcJ,
    phaseTransformedPolynomial, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  unfold candidate phaseC0 phaseC1 phaseC2 phaseC3 phaseC4 phaseC5 phaseC6
  dsimp only [Prod.fst, Prod.snd]
  ring

theorem parameterPhasePolynomial_zero_iff {p : ℝ × ℝ} {e t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    arcClearedDerivative p.1 p.2 e t = 0 ↔
      (parameterPhasePolynomial p e).eval (t / (1 - t)) = 0 := by
  have hd : 0 < 1 - t := sub_pos.mpr ht1
  have hu : 0 < 1 + t / (1 - t) := by positivity
  have hinv : (t / (1 - t)) / (1 + t / (1 - t)) = t := by field_simp; ring
  have h := parameterPhasePolynomial_transformed p e (t / (1 - t)) hu.ne'
  rw [hinv] at h
  have he : 1 + e ^ 2 ≠ 0 := by positivity
  have hz := congrArg (fun x : ℝ => x = 0) h
  simpa only [mul_eq_zero, pow_ne_zero 6 hu.ne', he, false_or] using hz.to_iff

@[fun_prop] private theorem contDiff_fixed_ite
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : E → F}
    (c : Prop) [Decidable c] (hf : ContDiff ℝ ω f) (hg : ContDiff ℝ ω g) :
    ContDiff ℝ ω (fun x => if c then f x else g x) := by
  by_cases h : c
  · simpa only [ite_eq_left h] using hf
  · simpa only [ite_eq_right h] using hg

set_option maxHeartbeats 0 in
-- Coefficient convolution produces several nested finite sums.
theorem contDiff_parameterPhasePolynomial_coeff (k : ℕ) :
    ContDiff ℝ ω (fun q : (ℝ × ℝ) × ℝ => (parameterPhasePolynomial q.1 q.2).coeff k) := by
  classical
  simp only [parameterPhasePolynomial, transformedArcD, transformedArcH, transformedArcJ,
    Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_mul, Polynomial.coeff_C,
    Polynomial.coeff_X, Polynomial.coeff_X_pow]
  fun_prop

end PiIrrationality
