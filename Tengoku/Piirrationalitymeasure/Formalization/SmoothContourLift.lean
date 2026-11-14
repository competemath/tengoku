import Tengoku.Piirrationalitymeasure.Formalization.ContourPath

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! A smooth parametrization of the square-root contour, including its zero endpoint. -/

namespace PiIrrationality

noncomputable def smoothArcCore (e u : ℝ) : ℂ :=
  ((-3 : ℂ) + 4 * Complex.I) / (1 - Complex.I * (e : ℂ) * (1 - (u : ℂ) ^ (2 : ℕ)))

noncomputable def smoothTauPlus (e u : ℝ) : ℂ := -(u : ℂ) * Complex.sqrt (smoothArcCore e u)

noncomputable def smoothTauMinus (e u : ℝ) : ℂ := star (smoothTauPlus e u)

theorem smoothArcCore_den_ne_zero (e u : ℝ) :
    1 - Complex.I * (e : ℂ) * (1 - (u : ℂ) ^ (2 : ℕ)) ≠ 0 := by
  have h := gammaPath_den_ne_zero e (u ^ (2 : ℕ))
  push_cast at h
  exact h

theorem smoothArcCore_im (e u : ℝ) :
    (smoothArcCore e u).im = (4 - 3 * e * (1 - u ^ 2)) / (1 + e ^ 2 * (1 - u ^ 2) ^ 2) := by
  unfold smoothArcCore
  rw [Complex.div_im]
  simp [Complex.normSq_apply, pow_two]
  ring

theorem smoothArcCore_im_pos {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (u : ℝ) :
    0 < (smoothArcCore e u).im := by
  rw [smoothArcCore_im]
  apply div_pos _ (by positivity)
  nlinarith [mul_nonneg he0 (sq_nonneg u)]

theorem smoothArcCore_mem_slitPlane {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (u : ℝ) :
    smoothArcCore e u ∈ Complex.slitPlane :=
  Or.inr (smoothArcCore_im_pos he0 he1 u).ne'

theorem smoothArcCore_gamma (e u : ℝ) :
    (u : ℂ) ^ (2 : ℕ) * smoothArcCore e u = gammaPath e (u ^ 2) := by
  unfold smoothArcCore gammaPath
  push_cast
  ring

theorem complex_sqrt_ofReal_sq_mul {u : ℝ} (hu : 0 ≤ u) {z : ℂ} (hz : 0 ≤ z.im) :
    Complex.sqrt ((u : ℂ) ^ (2 : ℕ) * z) = (u : ℂ) * Complex.sqrt z := by
  have hn : ‖(u : ℂ) ^ (2 : ℕ) * z‖ = u ^ 2 * ‖z‖ := by
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hr : ((u : ℂ) ^ (2 : ℕ) * z).re = u ^ 2 * z.re := by simp [pow_two, mul_assoc]
  have hi : ((u : ℂ) ^ (2 : ℕ) * z).im = u ^ 2 * z.im := by simp [pow_two, mul_assoc]
  have hip : 0 ≤ ((u : ℂ) ^ (2 : ℕ) * z).im := by rw [hi]; positivity
  have hp : Real.sqrt ((u ^ 2 * ‖z‖ + u ^ 2 * z.re) / 2) =
      u * Real.sqrt ((‖z‖ + z.re) / 2) := by
    rw [show (u ^ 2 * ‖z‖ + u ^ 2 * z.re) / 2 = u ^ 2 * ((‖z‖ + z.re) / 2) by ring,
      Real.sqrt_mul (sq_nonneg u), Real.sqrt_sq hu]
  have hm : Real.sqrt ((u ^ 2 * ‖z‖ - u ^ 2 * z.re) / 2) =
      u * Real.sqrt ((‖z‖ - z.re) / 2) := by
    rw [show (u ^ 2 * ‖z‖ - u ^ 2 * z.re) / 2 = u ^ 2 * ((‖z‖ - z.re) / 2) by ring,
      Real.sqrt_mul (sq_nonneg u), Real.sqrt_sq hu]
  rw [Complex.sqrt_eq_real_add_ite, ite_eq_left hip, Complex.sqrt_eq_real_add_ite, ite_eq_left hz,
    hn, hr, hp, hm]
  push_cast
  ring

theorem smoothTauPlus_eq {e u : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (hu : 0 ≤ u) :
    smoothTauPlus e u = tauPlus e (u ^ 2) := by
  rw [tauPlus, ← smoothArcCore_gamma, complex_sqrt_ofReal_sq_mul hu
    (smoothArcCore_im_pos he0 he1 u).le]
  unfold smoothTauPlus
  ring

theorem smoothTauMinus_eq {e u : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (hu : 0 ≤ u) :
    smoothTauMinus e u = tauMinus e (u ^ 2) := by
  rw [smoothTauMinus, smoothTauPlus_eq he0 he1 hu, tauMinus]

theorem smoothTauPlus_contDiff {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    ContDiff ℝ 1 (smoothTauPlus e) := by
  have hc : ContDiff ℝ 1 (smoothArcCore e) := by
    apply contDiff_iff_contDiffAt.mpr
    intro u
    have hf : ContDiffAt ℂ 1 (fun z : ℂ =>
        ((-3 : ℂ) + 4 * Complex.I) / (1 - Complex.I * (e : ℂ) * (1 - z ^ 2))) (u : ℂ) := by
      fun_prop (disch := exact smoothArcCore_den_ne_zero e u)
    exact (hf.restrict_scalars ℝ).comp u Complex.ofRealCLM.contDiff.contDiffAt
  have hs : ContDiff ℝ 1 (fun u => Complex.sqrt (smoothArcCore e u)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro u
    have hroot := (Complex.differentiableOn_sqrt.analyticOnNhd Complex.isOpen_slitPlane)
      _ (smoothArcCore_mem_slitPlane he0 he1 u)
    exact (hroot.contDiffAt.restrict_scalars ℝ).comp u hc.contDiffAt
  exact (Complex.ofRealCLM.contDiff.neg.mul hs)

theorem smoothTauMinus_contDiff {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    ContDiff ℝ 1 (smoothTauMinus e) :=
  Complex.conjCLE.contDiff.comp (smoothTauPlus_contDiff he0 he1)

theorem smoothTauPlus_at_zero (e : ℝ) : smoothTauPlus e 0 = 0 := by simp [smoothTauPlus]

theorem smoothTauMinus_at_zero (e : ℝ) : smoothTauMinus e 0 = 0 := by
  simp [smoothTauMinus, smoothTauPlus_at_zero]

theorem smoothTauPlus_at_one (e : ℝ) : smoothTauPlus e 1 = -1 - 2 * Complex.I := by
  norm_num [smoothTauPlus, smoothArcCore, complex_sqrt_neg_three_add_four_I]
  ring

theorem smoothTauMinus_at_one (e : ℝ) : smoothTauMinus e 1 = -1 + 2 * Complex.I := by
  simp [smoothTauMinus, smoothTauPlus_at_one]

theorem smoothTauPlus_norm_lt_five {e u : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : ‖smoothTauPlus e u‖ < 5 := by
  rw [smoothTauPlus_eq he0 he1 hu0]
  exact tauPlus_norm_lt_five (sq_nonneg u) (by nlinarith)

theorem smoothTauMinus_norm_lt_five {e u : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : ‖smoothTauMinus e u‖ < 5 := by
  rw [smoothTauMinus, norm_star]
  exact smoothTauPlus_norm_lt_five he0 he1 hu0 hu1

end PiIrrationality
