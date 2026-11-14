import Tengoku.Piirrationalitymeasure.Formalization.PhaseArc
import Tengoku.Piirrationalitymeasure.Formalization.PhaseSigns

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The real-valued complex phase (4.13), its restriction to the controlled arc,
and the positive-denominator derivative formula from Appendix A.3.
-/

namespace PiIrrationality

noncomputable def complexPhase (alpha beta : ℝ) (y : ℂ) : ℝ :=
  alpha * Real.log ‖y‖ + beta * Real.log ‖y ^ 2 + 6 * y + 25‖ -
    Real.log ‖25 - y‖

def arcD (e lambda : ℝ) : ℝ := 1 + e ^ 2 * (1 - lambda) ^ 2

theorem arcD_pos (e lambda : ℝ) : 0 < arcD e lambda := by
  unfold arcD
  positivity

theorem arcD_eq_normSq (e lambda : ℝ) :
    arcD e lambda = Complex.normSq (arcDen e lambda) := by
  exact (gammaPath_den_normSq e lambda).symm

theorem arcH_pos {e lambda : ℝ} (he : (9 : ℝ) / 10 < e)
    (hl0 : 0 ≤ lambda) (hl1 : lambda ≤ 1) : 0 < arcH e lambda := by
  rw [← arcK_normSq_eq]
  exact lt_trans (by norm_num) (arcK_normSq_gt he hl0 hl1)

theorem arcJ_pos {e lambda : ℝ} (he : (9 : ℝ) / 10 < e)
    (hl0 : 0 ≤ lambda) (hl1 : lambda ≤ 1) : 0 < arcJ e lambda := by
  rw [← arcL_normSq_eq]
  exact lt_of_lt_of_le (by norm_num) (arcL_normSq_ge he hl0 hl1)

theorem arc_quadratic_normSq (e lambda : ℝ) :
    Complex.normSq ((gammaPath e lambda) ^ 2 + 6 * gammaPath e lambda + 25) =
      (1 - lambda) ^ 2 * arcH e lambda / (arcD e lambda) ^ 2 := by
  rw [arc_quadratic_factorization, Complex.normSq_div, map_mul, map_pow,
    arcK_normSq_eq, ← arcD_eq_normSq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem arc_pole_normSq (e lambda : ℝ) :
    Complex.normSq (25 - gammaPath e lambda) = arcJ e lambda / arcD e lambda := by
  rw [arc_pole_factorization, Complex.normSq_div, arcL_normSq_eq, ← arcD_eq_normSq]

theorem log_complex_normSq (z : ℂ) :
    Real.log (Complex.normSq z) = 2 * Real.log ‖z‖ := by
  rw [← Complex.sq_norm, Real.log_pow]
  norm_num

noncomputable def arcLogPhase (alpha beta e lambda : ℝ) : ℝ :=
  alpha * Real.log 25 + 2 * alpha * Real.log lambda +
    2 * beta * Real.log (1 - lambda) + beta * Real.log (arcH e lambda) -
    Real.log (arcJ e lambda) + (1 - alpha - 2 * beta) * Real.log (arcD e lambda)

theorem twice_complexPhase_on_arc (alpha beta : ℝ) {e lambda : ℝ}
    (he : (9 : ℝ) / 10 < e) (hl0 : 0 < lambda) (hl1 : lambda < 1) :
    2 * complexPhase alpha beta (gammaPath e lambda) =
      arcLogPhase alpha beta e lambda := by
  have hH := (arcH_pos he hl0.le hl1.le).ne'
  have hJ := (arcJ_pos he hl0.le hl1.le).ne'
  have hD := (arcD_pos e lambda).ne'
  have hl := hl0.ne'
  have hl' : 1 - lambda ≠ 0 := (sub_pos.mpr hl1).ne'
  calc
    _ = alpha * Real.log (Complex.normSq (gammaPath e lambda)) +
        beta * Real.log (Complex.normSq
          ((gammaPath e lambda) ^ 2 + 6 * gammaPath e lambda + 25)) -
        Real.log (Complex.normSq (25 - gammaPath e lambda)) := by
      simp only [log_complex_normSq, complexPhase]
      ring
    _ = arcLogPhase alpha beta e lambda := by
      rw [arc_quadratic_normSq, arc_pole_normSq, gammaPath_normSq]
      change alpha * Real.log (25 * lambda ^ 2 / arcD e lambda) +
        beta * Real.log ((1 - lambda) ^ 2 * arcH e lambda / (arcD e lambda) ^ 2) -
        Real.log (arcJ e lambda / arcD e lambda) = _
      rw [Real.log_div (mul_ne_zero (by norm_num) (pow_ne_zero 2 hl)) hD,
        Real.log_mul (by norm_num : (25 : ℝ) ≠ 0) (pow_ne_zero 2 hl),
        Real.log_div (mul_ne_zero (pow_ne_zero 2 hl') hH) (pow_ne_zero 2 hD),
        Real.log_mul (pow_ne_zero 2 hl') hH, Real.log_div hJ hD]
      simp only [Real.log_pow, Nat.cast_ofNat, arcLogPhase]
      ring

def arcDderiv (e lambda : ℝ) : ℝ := -2 * e ^ 2 * (1 - lambda)

def arcHderiv (e lambda : ℝ) : ℝ :=
  (-1250 * e ^ 4 - 1200 * e ^ 3 - 900 * e ^ 2 - 1200 * e + 350) +
    2 * (625 * e ^ 4 + 1200 * e ^ 3 + 1250 * e ^ 2 + 1200 * e + 625) * lambda

def arcJderiv (e lambda : ℝ) : ℝ :=
  (-1250 * e ^ 2 + 200 * e + 150) + 2 * (625 * e ^ 2 - 200 * e + 25) * lambda

theorem hasDerivAt_arcD (e lambda : ℝ) :
    HasDerivAt (arcD e) (arcDderiv e lambda) lambda := by
  convert! ((((hasDerivAt_id lambda).const_sub 1).pow 2).const_mul (e ^ 2)).const_add 1
    using 1
  simp only [arcDderiv, id_eq]
  ring

private theorem hasDerivAt_quadratic (a b c x : ℝ) :
    HasDerivAt (fun y => a + b * y + c * y ^ 2) (b + 2 * c * x) x := by
  convert! (((hasDerivAt_id x).const_mul b).const_add a).add
    ((hasDerivAt_pow 2 x).const_mul c) using 1
  ring

theorem hasDerivAt_arcH (e lambda : ℝ) :
    HasDerivAt (arcH e) (arcHderiv e lambda) lambda := by
  exact hasDerivAt_quadratic _ _ _ _

theorem hasDerivAt_arcJ (e lambda : ℝ) :
    HasDerivAt (arcJ e) (arcJderiv e lambda) lambda := by
  exact hasDerivAt_quadratic _ _ _ _

noncomputable def arcLogPhaseDerivative (alpha beta e lambda : ℝ) : ℝ :=
  2 * alpha / lambda - 2 * beta / (1 - lambda) +
    beta * arcHderiv e lambda / arcH e lambda - arcJderiv e lambda / arcJ e lambda +
    (1 - alpha - 2 * beta) * arcDderiv e lambda / arcD e lambda

theorem hasDerivAt_arcLogPhase (alpha beta : ℝ) {e lambda : ℝ}
    (he : (9 : ℝ) / 10 < e) (hl0 : 0 < lambda) (hl1 : lambda < 1) :
    HasDerivAt (arcLogPhase alpha beta e)
      (arcLogPhaseDerivative alpha beta e lambda) lambda := by
  have hH := (hasDerivAt_arcH e lambda).log (arcH_pos he hl0.le hl1.le).ne'
  have hJ := (hasDerivAt_arcJ e lambda).log (arcJ_pos he hl0.le hl1.le).ne'
  have hD := (hasDerivAt_arcD e lambda).log (arcD_pos e lambda).ne'
  have hl := (hasDerivAt_id lambda).log hl0.ne'
  have hl' := ((hasDerivAt_id lambda).const_sub 1).log (sub_pos.mpr hl1).ne'
  have hsum := ((((hl.const_mul (2 * alpha)).const_add (alpha * Real.log 25)).add
    (hl'.const_mul (2 * beta))).add (hH.const_mul beta) |>.sub hJ).add
    (hD.const_mul (1 - alpha - 2 * beta))
  convert! hsum using 1
  simp only [arcLogPhaseDerivative, id_eq]
  ring

theorem hasDerivAt_twice_complexPhase_on_arc (alpha beta : ℝ) {e lambda : ℝ}
    (he : (9 : ℝ) / 10 < e) (hl0 : 0 < lambda) (hl1 : lambda < 1) :
    HasDerivAt (fun t => 2 * complexPhase alpha beta (gammaPath e t))
      (arcLogPhaseDerivative alpha beta e lambda) lambda := by
  apply (hasDerivAt_arcLogPhase alpha beta he hl0 hl1).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hl0 hl1] with t ht
  exact twice_complexPhase_on_arc alpha beta he ht.1 ht.2

theorem hasDerivAt_complexPhase_on_arc (alpha beta : ℝ) {e lambda : ℝ}
    (he : (9 : ℝ) / 10 < e) (hl0 : 0 < lambda) (hl1 : lambda < 1) :
    HasDerivAt (fun t => complexPhase alpha beta (gammaPath e t))
      (arcLogPhaseDerivative alpha beta e lambda / 2) lambda := by
  convert! (hasDerivAt_twice_complexPhase_on_arc alpha beta he hl0 hl1).div_const 2
    using 1
  funext t
  ring

def arcPhaseNumerator (e lambda : ℝ) : ℝ :=
  phaseC0 e * (1 - lambda) ^ 6 + phaseC1 e * lambda * (1 - lambda) ^ 5 +
    phaseC2 e * lambda ^ 2 * (1 - lambda) ^ 4 +
    phaseC3 e * lambda ^ 3 * (1 - lambda) ^ 3 +
    phaseC4 e * lambda ^ 4 * (1 - lambda) ^ 2 +
    phaseC5 e * lambda ^ 5 * (1 - lambda) + phaseC6 e * lambda ^ 6

def arcClearedDerivative (alpha beta e lambda : ℝ) : ℝ :=
  2 * alpha * (1 - lambda) * arcD e lambda * arcH e lambda * arcJ e lambda -
    2 * beta * lambda * arcD e lambda * arcH e lambda * arcJ e lambda +
    beta * lambda * (1 - lambda) * arcD e lambda * arcJ e lambda * arcHderiv e lambda -
    lambda * (1 - lambda) * arcD e lambda * arcH e lambda * arcJderiv e lambda +
    (1 - alpha - 2 * beta) * lambda * (1 - lambda) *
      arcH e lambda * arcJ e lambda * arcDderiv e lambda

theorem arcLogPhaseDerivative_cleared (alpha beta : ℝ) {e lambda : ℝ}
    (he : (9 : ℝ) / 10 < e) (hl0 : 0 < lambda) (hl1 : lambda < 1) :
    lambda * (1 - lambda) * arcD e lambda * arcH e lambda * arcJ e lambda *
        arcLogPhaseDerivative alpha beta e lambda =
      arcClearedDerivative alpha beta e lambda := by
  have hH := (arcH_pos he hl0.le hl1.le).ne'
  have hJ := (arcJ_pos he hl0.le hl1.le).ne'
  have hD := (arcD_pos e lambda).ne'
  have hl := hl0.ne'
  have hl' : 1 - lambda ≠ 0 := (sub_pos.mpr hl1).ne'
  unfold arcLogPhaseDerivative arcClearedDerivative
  field_simp [hH, hJ, hD, hl, hl']

theorem arcClearedDerivative_candidate (e lambda : ℝ) :
    arcClearedDerivative (1857 / 5570) (3714 / 5570) e lambda =
      (125 : ℝ) / 557 * (1 + e ^ 2) * arcPhaseNumerator e lambda := by
  unfold arcClearedDerivative arcPhaseNumerator arcD arcH arcJ arcDderiv arcHderiv arcJderiv
    phaseC0 phaseC1 phaseC2 phaseC3 phaseC4 phaseC5 phaseC6
  ring

theorem twice_complexPhase_deriv_cleared {e lambda : ℝ}
    (he : (9 : ℝ) / 10 < e) (hl0 : 0 < lambda) (hl1 : lambda < 1) :
    lambda * (1 - lambda) * arcD e lambda * arcH e lambda * arcJ e lambda *
        deriv (fun t => 2 * complexPhase (1857 / 5570) (3714 / 5570)
          (gammaPath e t)) lambda =
      (125 : ℝ) / 557 * (1 + e ^ 2) * arcPhaseNumerator e lambda := by
  rw [(hasDerivAt_twice_complexPhase_on_arc _ _ he hl0 hl1).deriv,
    arcLogPhaseDerivative_cleared _ _ he hl0 hl1, arcClearedDerivative_candidate]

theorem arcPhaseNumerator_transformed (e u : ℝ) (hu : 1 + u ≠ 0) :
    (1 + u) ^ 6 * arcPhaseNumerator e (u / (1 + u)) =
      (phaseTransformedPolynomial e).eval u := by
  simp only [arcPhaseNumerator, phaseTransformedPolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  field_simp [hu]
  ring

theorem arcPhaseNumerator_at_zero (e : ℝ) : arcPhaseNumerator e 0 = phaseC0 e := by
  simp [arcPhaseNumerator]

theorem arcPhaseNumerator_at_one (e : ℝ) : arcPhaseNumerator e 1 = phaseC6 e := by
  simp [arcPhaseNumerator]

theorem arcPhaseNumerator_zero_iff {e lambda : ℝ}
    (hl0 : 0 < lambda) (hl1 : lambda < 1) :
    arcPhaseNumerator e lambda = 0 ↔
      (phaseTransformedPolynomial e).eval (lambda / (1 - lambda)) = 0 := by
  have hden : 0 < 1 - lambda := sub_pos.mpr hl1
  have hu : 0 < 1 + lambda / (1 - lambda) := by positivity
  have hinv : (lambda / (1 - lambda)) / (1 + lambda / (1 - lambda)) = lambda := by
    field_simp
    ring
  have h := arcPhaseNumerator_transformed e (lambda / (1 - lambda)) hu.ne'
  rw [hinv] at h
  have hz := congrArg (fun x : ℝ => x = 0) h
  simpa only [mul_eq_zero, pow_ne_zero 6 hu.ne', false_or] using hz.to_iff

theorem arc_derivative_denominator_pos {e lambda : ℝ}
    (he : (9 : ℝ) / 10 < e) (hl0 : 0 < lambda) (hl1 : lambda < 1) :
    0 < lambda * (1 - lambda) * arcD e lambda * arcH e lambda * arcJ e lambda := by
  exact mul_pos (mul_pos (mul_pos (mul_pos hl0 (sub_pos.mpr hl1))
    (arcD_pos e lambda)) (arcH_pos he hl0.le hl1.le)) (arcJ_pos he hl0.le hl1.le)

theorem complexPhase_on_arc_deriv_zero_iff {e lambda : ℝ}
    (he : (9 : ℝ) / 10 < e) (hl0 : 0 < lambda) (hl1 : lambda < 1) :
    deriv (fun t => complexPhase (1857 / 5570) (3714 / 5570) (gammaPath e t)) lambda = 0 ↔
      arcPhaseNumerator e lambda = 0 := by
  have h := twice_complexPhase_deriv_cleared he hl0 hl1
  rw [(hasDerivAt_twice_complexPhase_on_arc _ _ he hl0 hl1).deriv] at h
  rw [(hasDerivAt_complexPhase_on_arc _ _ he hl0 hl1).deriv]
  have hden := (arc_derivative_denominator_pos he hl0 hl1).ne'
  have hfactor : (125 : ℝ) / 557 * (1 + e ^ 2) ≠ 0 := by positivity
  have hz := congrArg (fun x : ℝ => x = 0) h
  simpa only [div_eq_zero_iff, mul_eq_zero, hden, hfactor, false_or,
    OfNat.ofNat_ne_zero, or_false] using hz.to_iff

end PiIrrationality
