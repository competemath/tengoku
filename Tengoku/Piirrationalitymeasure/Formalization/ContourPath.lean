import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Algebraic identities for the complex contour in equations (4.15) and (4.22).
-/

namespace PiIrrationality

noncomputable def gammaPath (eta lambda : ℝ) : ℂ :=
  ((-3 : ℂ) + 4 * Complex.I) * (lambda : ℂ) /
    (1 - Complex.I * (eta : ℂ) * (1 - (lambda : ℂ)))

theorem gammaPath_den_normSq (eta lambda : ℝ) :
    Complex.normSq (1 - Complex.I * (eta : ℂ) * (1 - (lambda : ℂ))) =
      1 + eta ^ 2 * (1 - lambda) ^ 2 := by
  simp [Complex.normSq_apply]
  ring

theorem gammaPath_im (eta lambda : ℝ) :
    (gammaPath eta lambda).im =
      lambda * (4 - 3 * eta * (1 - lambda)) /
        (1 + eta ^ 2 * (1 - lambda) ^ 2) := by
  unfold gammaPath
  rw [Complex.div_im, gammaPath_den_normSq]
  simp [Complex.normSq_apply]
  ring

theorem gammaPath_normSq (eta lambda : ℝ) :
    Complex.normSq (gammaPath eta lambda) =
      25 * lambda ^ 2 / (1 + eta ^ 2 * (1 - lambda) ^ 2) := by
  unfold gammaPath
  rw [Complex.normSq_div, gammaPath_den_normSq]
  simp [Complex.normSq_apply]
  ring

theorem gammaPath_den_ne_zero (eta lambda : ℝ) :
    1 - Complex.I * (eta : ℂ) * (1 - (lambda : ℂ)) ≠ 0 := by
  intro hzero
  have hnorm := gammaPath_den_normSq eta lambda
  rw [hzero] at hnorm
  simp at hnorm
  nlinarith [sq_nonneg eta, sq_nonneg (1 - lambda)]

theorem gammaPath_at_one (eta : ℝ) :
    gammaPath eta 1 = (-3 : ℂ) + 4 * Complex.I := by
  unfold gammaPath
  norm_num

theorem complex_sqrt_neg_three_add_four_I :
    Complex.sqrt ((-3 : ℂ) + 4 * Complex.I) = 1 + 2 * Complex.I := by
  rw [Complex.sqrt_eq_real_add_ite]
  norm_num [Complex.norm_def, Complex.normSq_apply]

noncomputable def tauPlus (eta lambda : ℝ) : ℂ :=
  -Complex.sqrt (gammaPath eta lambda)

noncomputable def tauMinus (eta lambda : ℝ) : ℂ :=
  star (tauPlus eta lambda)

theorem gammaPath_at_zero (eta : ℝ) : gammaPath eta 0 = 0 := by
  unfold gammaPath
  simp

theorem tauPlus_at_zero (eta : ℝ) : tauPlus eta 0 = 0 := by
  simp [tauPlus, gammaPath_at_zero]

theorem tauPlus_at_one (eta : ℝ) :
    tauPlus eta 1 = -1 - 2 * Complex.I := by
  rw [tauPlus, gammaPath_at_one, complex_sqrt_neg_three_add_four_I]
  ring

theorem tauMinus_at_one (eta : ℝ) :
    tauMinus eta 1 = -1 + 2 * Complex.I := by
  rw [tauMinus, tauPlus_at_one]
  simp

theorem gammaPath_im_pos {eta lambda : ℝ}
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1) :
    0 < (gammaPath eta lambda).im := by
  rw [gammaPath_im]
  have hden : 0 < 1 + eta ^ 2 * (1 - lambda) ^ 2 := by positivity
  apply div_pos
  · have hterm : 0 ≤ eta * (1 - lambda) :=
      mul_nonneg heta0 (sub_nonneg.mpr hlambda1)
    have hterm_le : eta * (1 - lambda) ≤ 1 := by
      calc
        eta * (1 - lambda) ≤ eta * 1 := by
          exact mul_le_mul_of_nonneg_left (by linarith) heta0
        _ ≤ 1 := by simpa using heta1
    have hfactor : 0 < 4 - 3 * eta * (1 - lambda) := by linarith
    exact mul_pos hlambda0 hfactor
  · exact hden

theorem gammaPath_mem_slitPlane {eta lambda : ℝ}
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1) :
    gammaPath eta lambda ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  exact Or.inr (ne_of_gt (gammaPath_im_pos heta0 heta1 hlambda0 hlambda1))

theorem gammaPath_ne_zero {eta lambda : ℝ}
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1) :
    gammaPath eta lambda ≠ 0 := by
  intro hzero
  have him := gammaPath_im_pos heta0 heta1 hlambda0 hlambda1
  rw [hzero] at him
  simp at him

theorem sqrt_differentiableAt_gammaPath {eta lambda : ℝ}
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1) :
    DifferentiableAt ℂ Complex.sqrt (gammaPath eta lambda) :=
  Complex.differentiableAt_sqrt (gammaPath_mem_slitPlane heta0 heta1 hlambda0 hlambda1)

theorem sqrt_continuousAt_gammaPath {eta lambda : ℝ}
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1) :
    ContinuousAt Complex.sqrt (gammaPath eta lambda) :=
  Complex.continuousAt_sqrt (Or.inr (ne_of_gt (gammaPath_im_pos heta0 heta1 hlambda0 hlambda1)))

theorem complex_sqrt_sq (z : ℂ) : (Complex.sqrt z) ^ 2 = z := by
  unfold Complex.sqrt
  rw [← Complex.cpow_natCast]
  have hlow : -Real.pi < (Complex.log z * (2⁻¹ : ℂ)).im := by
    norm_num [Complex.mul_im, Complex.log_im]
    nlinarith [Complex.neg_pi_lt_arg z, Real.pi_pos]
  have hupp : (Complex.log z * (2⁻¹ : ℂ)).im ≤ Real.pi := by
    norm_num [Complex.mul_im, Complex.log_im]
    nlinarith [Complex.arg_le_pi z, Real.pi_pos]
  change (z ^ (2⁻¹ : ℂ)) ^ (2 : ℂ) = z
  rw [← Complex.cpow_mul (z := (2 : ℂ)) hlow hupp]
  norm_num

theorem tauPlus_sq {eta lambda : ℝ} :
    (tauPlus eta lambda) ^ 2 = gammaPath eta lambda := by
  rw [tauPlus]
  simpa using (complex_sqrt_sq (gammaPath eta lambda))

theorem tauMinus_sq {eta lambda : ℝ} :
    (tauMinus eta lambda) ^ 2 = star (gammaPath eta lambda) := by
  rw [tauMinus, pow_two, ← star_mul, ← pow_two, tauPlus_sq]

theorem complex_sqrt_ne_zero {z : ℂ} (hz : z ≠ 0) : Complex.sqrt z ≠ 0 := by
  intro hs
  unfold Complex.sqrt at hs
  rw [Complex.cpow_def] at hs
  simp [hz] at hs

theorem tauPlus_ne_zero {eta lambda : ℝ}
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1) :
    tauPlus eta lambda ≠ 0 := by
  intro hzero
  apply complex_sqrt_ne_zero (gammaPath_ne_zero heta0 heta1 hlambda0 hlambda1)
  simpa [tauPlus] using hzero

theorem gammaPath_norm_le_five {eta lambda : ℝ}
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    ‖gammaPath eta lambda‖ ≤ 5 := by
  have hden : 0 < 1 + eta ^ 2 * (1 - lambda) ^ 2 := by positivity
  have hsq : ‖gammaPath eta lambda‖ ^ 2 ≤ (5 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, gammaPath_normSq]
    apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg eta, sq_nonneg (1 - lambda)]
  exact (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp hsq

theorem tauPlus_norm_sq {eta lambda : ℝ} :
    ‖tauPlus eta lambda‖ ^ 2 = ‖gammaPath eta lambda‖ := by
  rw [← norm_pow, tauPlus_sq]

theorem tauPlus_norm_le_sqrt_five {eta lambda : ℝ}
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    ‖tauPlus eta lambda‖ ≤ Real.sqrt 5 := by
  have hgamma : ‖gammaPath eta lambda‖ ≤ (5 : ℝ) :=
    gammaPath_norm_le_five hlambda0 hlambda1
  have hsq : ‖tauPlus eta lambda‖ ^ 2 ≤ (Real.sqrt 5) ^ 2 := by
    rw [tauPlus_norm_sq, Real.sq_sqrt (by norm_num)]
    exact hgamma
  exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp hsq

theorem tauPlus_norm_lt_five {eta lambda : ℝ}
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    ‖tauPlus eta lambda‖ < 5 := by
  have hbound := tauPlus_norm_le_sqrt_five (eta := eta) hlambda0 hlambda1
  have hsqrt : Real.sqrt (5 : ℝ) < 5 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5), Real.sqrt_nonneg (5 : ℝ)]
  linarith

theorem tauMinus_norm_eq_tauPlus_norm (eta lambda : ℝ) :
    ‖tauMinus eta lambda‖ = ‖tauPlus eta lambda‖ := by
  rw [tauMinus]
  exact norm_star _

theorem tauMinus_norm_lt_five {eta lambda : ℝ}
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    ‖tauMinus eta lambda‖ < 5 := by
  rw [tauMinus_norm_eq_tauPlus_norm]
  exact tauPlus_norm_lt_five hlambda0 hlambda1

end PiIrrationality
