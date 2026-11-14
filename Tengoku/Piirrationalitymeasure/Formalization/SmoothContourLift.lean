import Tengoku.Piirrationalitymeasure.Formalization.ContourPath

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! A smooth parametrization of the square-root contour, including its zero endpoint. -/

namespace PiIrrationality

noncomputable def smoothArcCore (e u : ℝ) : ℂ :=
  ((-3 : ℂ) + 4 * Complex.I) / (1 - Complex.I * (e : ℂ) * (1 - (u : ℂ) ^ (2 : ℕ)))

noncomputable def smoothTauPlus (e u : ℝ) : ℂ := -(u : ℂ) * Complex.sqrt (smoothArcCore e u)

noncomputable def smoothTauMinus (e u : ℝ) : ℂ := star (smoothTauPlus e u)

/--
@isnad1 id=ne.0h2v.s6.b39aa81a255a from=translated src=- shape=ebc66dde vocab=882d04c2
-/
theorem smoothArcCore_den_ne_zero (e u : ℝ) :
    1 - Complex.I * (e : ℂ) * (1 - (u : ℂ) ^ (2 : ℕ)) ≠ 0 := by
  have h := gammaPath_den_ne_zero e (u ^ (2 : ℕ))
  push_cast at h
  exact h

/--
@isnad1 id=eq.0h2v.s7.b69175493bbe from=translated src=- shape=3172f379 vocab=b7098cc2
-/
theorem smoothArcCore_im (e u : ℝ) :
    (smoothArcCore e u).im = (4 - 3 * e * (1 - u ^ 2)) / (1 + e ^ 2 * (1 - u ^ 2) ^ 2) := by
  unfold smoothArcCore
  rw [Complex.div_im]
  simp [Complex.normSq_apply, pow_two]
  ring

/--
@isnad1 id=lt.2h2v.s5.602851a8c205 from=translated src=- shape=65c11151 vocab=ae251c95
-/
theorem smoothArcCore_im_pos {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (u : ℝ) :
    0 < (smoothArcCore e u).im := by
  rw [smoothArcCore_im]
  apply div_pos _ (by positivity)
  nlinarith [mul_nonneg he0 (sq_nonneg u)]

/--
@isnad1 id=mem.2h2v.s5.9cd01b800cc6 from=translated src=- shape=fd550a87 vocab=7bbad3f4
-/
theorem smoothArcCore_mem_slitPlane {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (u : ℝ) :
    smoothArcCore e u ∈ Complex.slitPlane :=
  Or.inr (smoothArcCore_im_pos he0 he1 u).ne'

/--
@isnad1 id=eq.0h2v.s5.8c2d262401c6 from=translated src=- shape=52160c57 vocab=ec460b5c
-/
theorem smoothArcCore_gamma (e u : ℝ) :
    (u : ℂ) ^ (2 : ℕ) * smoothArcCore e u = gammaPath e (u ^ 2) := by
  unfold smoothArcCore gammaPath
  push_cast
  ring

/--
@isnad1 id=eq.2h2v.s6.9ae6918d064f from=translated src=- shape=c4ea820f vocab=84de937d
-/
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

/--
@isnad1 id=eq.3h2v.s5.de96631ca955 from=translated src=- shape=8c673bb5 vocab=39325f9f
-/
theorem smoothTauPlus_eq {e u : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (hu : 0 ≤ u) :
    smoothTauPlus e u = tauPlus e (u ^ 2) := by
  rw [tauPlus, ← smoothArcCore_gamma, complex_sqrt_ofReal_sq_mul hu
    (smoothArcCore_im_pos he0 he1 u).le]
  unfold smoothTauPlus
  ring

/--
@isnad1 id=eq.3h2v.s5.0f66d8bf652d from=translated src=- shape=8c673bb5 vocab=08cd5b97
-/
theorem smoothTauMinus_eq {e u : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (hu : 0 ≤ u) :
    smoothTauMinus e u = tauMinus e (u ^ 2) := by
  rw [smoothTauMinus, smoothTauPlus_eq he0 he1 hu, tauMinus]

/--
@isnad1 id=contdiff.2h1v.s5.231984263b1e from=translated src=- shape=6b9542b5 vocab=66607290
-/
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

/--
@isnad1 id=contdiff.2h1v.s5.cc80c8785d6a from=translated src=- shape=6b9542b5 vocab=ff34fc1f
-/
theorem smoothTauMinus_contDiff {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    ContDiff ℝ 1 (smoothTauMinus e) :=
  Complex.conjCLE.contDiff.comp (smoothTauPlus_contDiff he0 he1)

/--
@isnad1 id=eq.0h1v.s4.3ea9acfdaad0 from=translated src=- shape=8fc7241c vocab=0d8b7d23
-/
theorem smoothTauPlus_at_zero (e : ℝ) : smoothTauPlus e 0 = 0 := by simp [smoothTauPlus]

/--
@isnad1 id=eq.0h1v.s4.760994a62cf6 from=translated src=- shape=8fc7241c vocab=bc7c35cf
-/
theorem smoothTauMinus_at_zero (e : ℝ) : smoothTauMinus e 0 = 0 := by
  simp [smoothTauMinus, smoothTauPlus_at_zero]

/--
@isnad1 id=eq.0h1v.s5.7db8840a7093 from=translated src=- shape=e308bea7 vocab=0615d2a9
-/
theorem smoothTauPlus_at_one (e : ℝ) : smoothTauPlus e 1 = -1 - 2 * Complex.I := by
  norm_num [smoothTauPlus, smoothArcCore, complex_sqrt_neg_three_add_four_I]
  ring

/--
@isnad1 id=eq.0h1v.s5.9142ca450247 from=translated src=- shape=e308bea7 vocab=e62d4c78
-/
theorem smoothTauMinus_at_one (e : ℝ) : smoothTauMinus e 1 = -1 + 2 * Complex.I := by
  simp [smoothTauMinus, smoothTauPlus_at_one]

/--
@isnad1 id=lt.4h2v.s6.3074809ec5ab from=translated src=- shape=2385c318 vocab=eef7f49b
-/
theorem smoothTauPlus_norm_lt_five {e u : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : ‖smoothTauPlus e u‖ < 5 := by
  rw [smoothTauPlus_eq he0 he1 hu0]
  exact tauPlus_norm_lt_five (sq_nonneg u) (by nlinarith)

/--
@isnad1 id=lt.4h2v.s6.f744d13e9485 from=translated src=- shape=2385c318 vocab=db4bb3fb
-/
theorem smoothTauMinus_norm_lt_five {e u : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : ‖smoothTauMinus e u‖ < 5 := by
  rw [smoothTauMinus, norm_star]
  exact smoothTauPlus_norm_lt_five he0 he1 hu0 hu1

end PiIrrationality
