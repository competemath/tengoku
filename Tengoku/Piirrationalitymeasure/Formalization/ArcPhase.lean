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

/--
@isnad1 id=lt.0h2v.s4.a29da422261a from=translated src=- shape=a120b2a8 vocab=f80056cb
-/
theorem arcD_pos (e lambda : ℝ) : 0 < arcD e lambda := by
  unfold arcD
  positivity

/--
@isnad1 id=eq.0h2v.s5.e8eeb63e5948 from=translated src=- shape=0596bc7b vocab=750f4484
-/
theorem arcD_eq_normSq (e lambda : ℝ) :
    arcD e lambda = Complex.normSq (arcDen e lambda) := by
  exact (gammaPath_den_normSq e lambda).symm

/--
@isnad1 id=lt.3h2v.s6.edd8c595c45d from=translated src=- shape=59c55472 vocab=6def50d4
-/
theorem arcH_pos {e lambda : ℝ} (he : (9 : ℝ) / 10 < e)
    (hl0 : 0 ≤ lambda) (hl1 : lambda ≤ 1) : 0 < arcH e lambda := by
  rw [← arcK_normSq_eq]
  exact lt_trans (by norm_num) (arcK_normSq_gt he hl0 hl1)

/--
@isnad1 id=lt.3h2v.s6.9cc75443ee06 from=translated src=- shape=59c55472 vocab=2458b487
-/
theorem arcJ_pos {e lambda : ℝ} (he : (9 : ℝ) / 10 < e)
    (hl0 : 0 ≤ lambda) (hl1 : lambda ≤ 1) : 0 < arcJ e lambda := by
  rw [← arcL_normSq_eq]
  exact lt_of_lt_of_le (by norm_num) (arcL_normSq_ge he hl0 hl1)

/--
@isnad1 id=eq.0h2v.s7.7c4a7a7ba2f6 from=translated src=- shape=da6dc413 vocab=775781c6
-/
theorem arc_quadratic_normSq (e lambda : ℝ) :
    Complex.normSq ((gammaPath e lambda) ^ 2 + 6 * gammaPath e lambda + 25) =
      (1 - lambda) ^ 2 * arcH e lambda / (arcD e lambda) ^ 2 := by
  rw [arc_quadratic_factorization, Complex.normSq_div, map_mul, map_pow,
    arcK_normSq_eq, ← arcD_eq_normSq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/--
@isnad1 id=eq.0h2v.s5.c0ce45cdd48e from=translated src=- shape=20f76de9 vocab=739eab8d
-/
theorem arc_pole_normSq (e lambda : ℝ) :
    Complex.normSq (25 - gammaPath e lambda) = arcJ e lambda / arcD e lambda := by
  rw [arc_pole_factorization, Complex.normSq_div, arcL_normSq_eq, ← arcD_eq_normSq]

/--
@isnad1 id=eq.0h1v.s5.7da6eceb1c9d from=translated src=- shape=2b4da8b8 vocab=6407fe89
-/
theorem log_complex_normSq (z : ℂ) :
    Real.log (Complex.normSq z) = 2 * Real.log ‖z‖ := by
  rw [← Complex.sq_norm, Real.log_pow]
  norm_num

noncomputable def arcLogPhase (alpha beta e lambda : ℝ) : ℝ :=
  alpha * Real.log 25 + 2 * alpha * Real.log lambda +
    2 * beta * Real.log (1 - lambda) + beta * Real.log (arcH e lambda) -
    Real.log (arcJ e lambda) + (1 - alpha - 2 * beta) * Real.log (arcD e lambda)

/--
@isnad1 id=eq.3h4v.s6.00147c984d12 from=translated src=- shape=1a6e9d80 vocab=f1f10850
-/
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

/--
@isnad1 id=hasderiv.0h2v.s5.7e8d7ffcb1bf from=translated src=- shape=d9353bef vocab=b1962a63
-/
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

/--
@isnad1 id=hasderiv.0h2v.s5.0aea4797cee2 from=translated src=- shape=d9353bef vocab=bab8e45c
-/
theorem hasDerivAt_arcH (e lambda : ℝ) :
    HasDerivAt (arcH e) (arcHderiv e lambda) lambda := by
  exact hasDerivAt_quadratic _ _ _ _

/--
@isnad1 id=hasderiv.0h2v.s5.225d46170852 from=translated src=- shape=d9353bef vocab=8ed411f9
-/
theorem hasDerivAt_arcJ (e lambda : ℝ) :
    HasDerivAt (arcJ e) (arcJderiv e lambda) lambda := by
  exact hasDerivAt_quadratic _ _ _ _

noncomputable def arcLogPhaseDerivative (alpha beta e lambda : ℝ) : ℝ :=
  2 * alpha / lambda - 2 * beta / (1 - lambda) +
    beta * arcHderiv e lambda / arcH e lambda - arcJderiv e lambda / arcJ e lambda +
    (1 - alpha - 2 * beta) * arcDderiv e lambda / arcD e lambda

/--
@isnad1 id=hasderiv.3h4v.s6.9671afa53a57 from=translated src=- shape=3be7416a vocab=76815965
-/
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

/--
@isnad1 id=hasderiv.3h4v.s6.9dc1e0d73bba from=translated src=- shape=6b47c7dd vocab=d5ea69be
-/
theorem hasDerivAt_twice_complexPhase_on_arc (alpha beta : ℝ) {e lambda : ℝ}
    (he : (9 : ℝ) / 10 < e) (hl0 : 0 < lambda) (hl1 : lambda < 1) :
    HasDerivAt (fun t => 2 * complexPhase alpha beta (gammaPath e t))
      (arcLogPhaseDerivative alpha beta e lambda) lambda := by
  apply (hasDerivAt_arcLogPhase alpha beta he hl0 hl1).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hl0 hl1] with t ht
  exact twice_complexPhase_on_arc alpha beta he ht.1 ht.2

/--
@isnad1 id=hasderiv.3h4v.s6.8b4f55ba3e85 from=translated src=- shape=0928cb69 vocab=855a07d8
-/
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

/--
@isnad1 id=eq.3h4v.s7.fdf94346e181 from=translated src=- shape=47f9fbe2 vocab=1d9f2453
-/
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

/--
@isnad1 id=eq.0h2v.s7.c598e844ae95 from=translated src=- shape=98b22375 vocab=4ead2804
-/
theorem arcClearedDerivative_candidate (e lambda : ℝ) :
    arcClearedDerivative (1857 / 5570) (3714 / 5570) e lambda =
      (125 : ℝ) / 557 * (1 + e ^ 2) * arcPhaseNumerator e lambda := by
  unfold arcClearedDerivative arcPhaseNumerator arcD arcH arcJ arcDderiv arcHderiv arcJderiv
    phaseC0 phaseC1 phaseC2 phaseC3 phaseC4 phaseC5 phaseC6
  ring

/--
@isnad1 id=eq.3h2v.s8.648e301a2b10 from=translated src=- shape=f1d5dfea vocab=2e7822bf
-/
theorem twice_complexPhase_deriv_cleared {e lambda : ℝ}
    (he : (9 : ℝ) / 10 < e) (hl0 : 0 < lambda) (hl1 : lambda < 1) :
    lambda * (1 - lambda) * arcD e lambda * arcH e lambda * arcJ e lambda *
        deriv (fun t => 2 * complexPhase (1857 / 5570) (3714 / 5570)
          (gammaPath e t)) lambda =
      (125 : ℝ) / 557 * (1 + e ^ 2) * arcPhaseNumerator e lambda := by
  rw [(hasDerivAt_twice_complexPhase_on_arc _ _ he hl0 hl1).deriv,
    arcLogPhaseDerivative_cleared _ _ he hl0 hl1, arcClearedDerivative_candidate]

/--
@isnad1 id=eq.1h2v.s6.fd17cdab616b from=translated src=- shape=ba07f93b vocab=90ff5609
-/
theorem arcPhaseNumerator_transformed (e u : ℝ) (hu : 1 + u ≠ 0) :
    (1 + u) ^ 6 * arcPhaseNumerator e (u / (1 + u)) =
      (phaseTransformedPolynomial e).eval u := by
  simp only [arcPhaseNumerator, phaseTransformedPolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  field_simp [hu]
  ring

/--
@isnad1 id=eq.0h1v.s3.093e60fb23ba from=translated src=- shape=53eb01b5 vocab=487621a4
-/
theorem arcPhaseNumerator_at_zero (e : ℝ) : arcPhaseNumerator e 0 = phaseC0 e := by
  simp [arcPhaseNumerator]

/--
@isnad1 id=eq.0h1v.s3.374a41584f1f from=translated src=- shape=53eb01b5 vocab=c9633fc7
-/
theorem arcPhaseNumerator_at_one (e : ℝ) : arcPhaseNumerator e 1 = phaseC6 e := by
  simp [arcPhaseNumerator]

/--
@isnad1 id=iff.2h2v.s6.54c18ec15192 from=translated src=- shape=06e74197 vocab=a0a718d5
-/
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

/--
@isnad1 id=lt.3h2v.s6.a4c581423672 from=translated src=- shape=8937fdd6 vocab=88b91bc9
-/
theorem arc_derivative_denominator_pos {e lambda : ℝ}
    (he : (9 : ℝ) / 10 < e) (hl0 : 0 < lambda) (hl1 : lambda < 1) :
    0 < lambda * (1 - lambda) * arcD e lambda * arcH e lambda * arcJ e lambda := by
  exact mul_pos (mul_pos (mul_pos (mul_pos hl0 (sub_pos.mpr hl1))
    (arcD_pos e lambda)) (arcH_pos he hl0.le hl1.le)) (arcJ_pos he hl0.le hl1.le)

/--
@isnad1 id=iff.3h2v.s7.53844896cdd6 from=translated src=- shape=249c9d99 vocab=2a020ab7
-/
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
