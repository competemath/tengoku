import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Beta
import Tengoku.Seed.RingTheory.Polynomial.Pochhammer
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms Row12.gammaMoment_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.gammaMoment_pos` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.gammaMoment_succ` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.gammaMoment_le_one` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.gammaMoment_eq_ascPochhammer` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.complexBeta_eq_realBeta` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.realBeta_integrable` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.realBeta_eq_gamma` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.realBeta_pos` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.realBeta_one_sub` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.gammaMoment_eq_beta_ratio` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.betaKernel_moment_integrable` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.betaKernel_moment_integral` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.betaDensity_moment_integrable` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.betaDensity_moment_integral` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.betaDensity_integral` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.betaDensity_nonneg` (it only prints; the queue checks the axioms of every declaration). -/

open MeasureTheory Set intervalIntegral

namespace Row12

noncomputable def gammaMoment (a : ℝ) (n : ℕ) : ℝ :=
  Real.Gamma (a + n) / (Real.Gamma a * (Nat.factorial n : ℝ))

noncomputable def realBeta (u v : ℝ) : ℝ :=
  ∫ x : ℝ in 0..1, x ^ (u - 1) * (1 - x) ^ (v - 1)

noncomputable def betaKernel (a x : ℝ) : ℝ :=
  x ^ (a - 1) * (1 - x) ^ (-a)

noncomputable def betaDensity (a x : ℝ) : ℝ :=
  betaKernel a x / (Real.Gamma a * Real.Gamma (1 - a))

/--
@isnad1 id=eq.1h1v.s4.09be557ede5d from=translated src=- shape=f9fa777c vocab=40465c1a
-/
theorem gammaMoment_zero {a : ℝ} (ha : 0 < a) : gammaMoment a 0 = 1 := by
  simp [gammaMoment, (Real.Gamma_pos_of_pos ha).ne']

/--
@isnad1 id=lt.1h2v.s4.b4434f2d6e32 from=translated src=- shape=9141f3a7 vocab=40465c1a
-/
theorem gammaMoment_pos {a : ℝ} (ha : 0 < a) (n : ℕ) : 0 < gammaMoment a n := by
  exact div_pos (Real.Gamma_pos_of_pos (by positivity))
    (mul_pos (Real.Gamma_pos_of_pos ha) (by positivity))

/--
@isnad1 id=eq.1h2v.s6.b6eefb79bc6b from=translated src=- shape=7fcac427 vocab=51666ffe
-/
theorem gammaMoment_succ {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ((n : ℝ) + 1) * gammaMoment a (n + 1) = ((n : ℝ) + a) * gammaMoment a n := by
  have hga : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have han : a + (n : ℝ) ≠ 0 := by positivity
  simp only [gammaMoment, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [show a + ((n : ℝ) + 1) = (a + (n : ℝ)) + 1 by ring,
    Real.Gamma_add_one han]
  field_simp [hga, hfac, hn]
  ring

/--
@isnad1 id=le.2h2v.s5.9ce19e3203cd from=translated src=- shape=624ee336 vocab=ae552131
-/
theorem gammaMoment_le_one {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (n : ℕ) :
    gammaMoment a n ≤ 1 := by
  induction n with
  | zero => rw [gammaMoment_zero ha]
  | succ n ih =>
    apply (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mp
    rw [gammaMoment_succ ha n]
    calc
      ((n : ℝ) + a) * gammaMoment a n ≤ ((n : ℝ) + a) * 1 :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ ≤ ((n : ℝ) + 1) * 1 := by linarith

/--
@isnad1 id=eq.1h2v.s5.205a4c69e823 from=translated src=- shape=2bf734f1 vocab=34f0b2c8
-/
theorem gammaMoment_eq_ascPochhammer {a : ℝ} (ha : 0 < a) (n : ℕ) :
    gammaMoment a n = (ascPochhammer ℝ n).eval a / (Nat.factorial n : ℝ) := by
  induction n with
  | zero => simp [gammaMoment_zero ha]
  | succ n ih =>
    have hfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    apply (mul_left_cancel₀ hn)
    rw [gammaMoment_succ ha n, ih, ascPochhammer_succ_eval, Nat.factorial_succ]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp [hfac, hn]
    ring

private theorem beta_integrand_cast (u v x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    ((x ^ (u - 1) * (1 - x) ^ (v - 1) : ℝ) : ℂ) =
      (x : ℂ) ^ ((u : ℂ) - 1) * (1 - (x : ℂ)) ^ ((v : ℂ) - 1) := by
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hx (u - 1),
    Complex.ofReal_cpow (sub_nonneg.mpr hx1) (v - 1)]
  push_cast
  rfl

/--
@isnad1 id=eq.0h2v.s3.97d854b8ad9c from=translated src=- shape=44b05f7b vocab=1373d1e7
-/
theorem complexBeta_eq_realBeta (u v : ℝ) :
    Complex.betaIntegral (u : ℂ) (v : ℂ) = (realBeta u v : ℂ) := by
  calc
    Complex.betaIntegral (u : ℂ) (v : ℂ) =
        ∫ x : ℝ in 0..1, ((x ^ (u - 1) * (1 - x) ^ (v - 1) : ℝ) : ℂ) := by
      unfold Complex.betaIntegral
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le zero_le_one] at hx
      exact (beta_integrand_cast u v x hx.1 hx.2).symm
    _ = (realBeta u v : ℂ) := intervalIntegral.integral_ofReal

/--
@isnad1 id=interval.2h2v.s6.e17eb9a65a66 from=translated src=- shape=d58221b5 vocab=0bf28822
-/
theorem realBeta_integrable {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    IntervalIntegrable (fun x : ℝ => x ^ (u - 1) * (1 - x) ^ (v - 1)) volume 0 1 := by
  have hc := Complex.betaIntegral_convergent
    (u := (u : ℂ)) (v := (v : ℂ)) (by simpa using hu) (by simpa using hv)
  have hr : IntervalIntegrable
      (fun x : ℝ => ((x : ℂ) ^ ((u : ℂ) - 1) *
        (1 - (x : ℂ)) ^ ((v : ℂ) - 1)).re) volume 0 1 := ⟨hc.1.re, hc.2.re⟩
  apply hr.congr_uIoo
  intro x hx
  rw [uIoo_of_lt zero_lt_one] at hx
  change ((x : ℂ) ^ ((u : ℂ) - 1) * (1 - (x : ℂ)) ^ ((v : ℂ) - 1)).re = _
  rw [← beta_integrand_cast u v x hx.1.le hx.2.le, Complex.ofReal_re]

/--
@isnad1 id=eq.2h2v.s5.ff5ea155bfba from=translated src=- shape=9e91afd8 vocab=6404ea03
-/
theorem realBeta_eq_gamma {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    realBeta u v = Real.Gamma u * Real.Gamma v / Real.Gamma (u + v) := by
  apply Complex.ofReal_injective
  rw [← complexBeta_eq_realBeta, Complex.betaIntegral_eq_Gamma_mul_div
    _ _ (by simpa using hu) (by simpa using hv), ← Complex.ofReal_add]
  simp only [Complex.Gamma_ofReal, Complex.ofReal_mul, Complex.ofReal_div]

/--
@isnad1 id=lt.2h2v.s5.7e9912632c93 from=translated src=- shape=6c67d60b vocab=c8bf40dc
-/
theorem realBeta_pos {u v : ℝ} (hu : 0 < u) (hv : 0 < v) : 0 < realBeta u v := by
  rw [realBeta_eq_gamma hu hv]
  exact div_pos (mul_pos (Real.Gamma_pos_of_pos hu) (Real.Gamma_pos_of_pos hv))
    (Real.Gamma_pos_of_pos (add_pos hu hv))

/--
@isnad1 id=eq.2h1v.s6.34d632506f25 from=translated src=- shape=72eccd3a vocab=caaa3b2c
-/
theorem realBeta_one_sub {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    realBeta a (1 - a) = Real.Gamma a * Real.Gamma (1 - a) := by
  rw [realBeta_eq_gamma ha (sub_pos.mpr ha1),
    show a + (1 - a) = 1 by ring, Real.Gamma_one, div_one]

/--
@isnad1 id=eq.2h2v.s6.4a708a84072e from=translated src=- shape=87539d68 vocab=b8eeea9c
-/
theorem gammaMoment_eq_beta_ratio {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (n : ℕ) :
    gammaMoment a n = realBeta (a + n) (1 - a) / realBeta a (1 - a) := by
  rw [realBeta_eq_gamma (by positivity) (sub_pos.mpr ha1), realBeta_one_sub ha ha1,
    show a + (n : ℝ) + (1 - a) = (n : ℝ) + 1 by ring,
    Real.Gamma_nat_eq_factorial, gammaMoment]
  have hga : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hgb : Real.Gamma (1 - a) ≠ 0 := (Real.Gamma_pos_of_pos (sub_pos.mpr ha1)).ne'
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  field_simp [hga, hgb, hfac]

private theorem beta_moment_integrand {a x : ℝ} (n : ℕ) (hx : 0 < x) :
    x ^ (a + (n : ℝ) - 1) * (1 - x) ^ ((1 - a) - 1) =
      x ^ n * betaKernel a x := by
  rw [show a + (n : ℝ) - 1 = (a - 1) + (n : ℝ) by ring,
    Real.rpow_add hx, Real.rpow_natCast, show (1 - a) - 1 = -a by ring]
  unfold betaKernel
  ring

/--
@isnad1 id=interval.2h2v.s6.f7b31da2af6d from=translated src=- shape=c6a5fc9f vocab=274cf9ec
-/
theorem betaKernel_moment_integrable {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (n : ℕ) :
    IntervalIntegrable (fun x : ℝ => x ^ n * betaKernel a x) volume 0 1 := by
  apply (realBeta_integrable (u := a + n) (by positivity) (sub_pos.mpr ha1)).congr_uIoo
  intro x hx
  rw [uIoo_of_lt zero_lt_one] at hx
  exact beta_moment_integrand n hx.1

/--
@isnad1 id=eq.2h2v.s6.b5a332f71343 from=translated src=- shape=9d867b96 vocab=0c1842ec
-/
theorem betaKernel_moment_integral {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (n : ℕ) :
    (∫ x : ℝ in 0..1, x ^ n * betaKernel a x) /
      (Real.Gamma a * Real.Gamma (1 - a)) = gammaMoment a n := by
  rw [gammaMoment_eq_beta_ratio ha ha1, realBeta_one_sub ha ha1]
  congr 1
  unfold realBeta
  apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
  intro x hx
  exact (beta_moment_integrand n hx.1).symm

/--
@isnad1 id=interval.2h2v.s6.d83fd87873a5 from=translated src=- shape=c6a5fc9f vocab=48f1c8d8
-/
theorem betaDensity_moment_integrable {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (n : ℕ) :
    IntervalIntegrable (fun x : ℝ => x ^ n * betaDensity a x) volume 0 1 := by
  simpa only [betaDensity, mul_div_assoc] using
    (betaKernel_moment_integrable ha ha1 n).div_const
      (Real.Gamma a * Real.Gamma (1 - a))

/--
@isnad1 id=eq.2h2v.s6.04a82bcb6b15 from=translated src=- shape=3167d9c6 vocab=548dfa68
-/
theorem betaDensity_moment_integral {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (n : ℕ) :
    (∫ x : ℝ in 0..1, x ^ n * betaDensity a x) = gammaMoment a n := by
  simp only [betaDensity, ← mul_div_assoc, intervalIntegral.integral_div]
  exact betaKernel_moment_integral ha ha1 n

/--
@isnad1 id=eq.2h1v.s6.582394b74e84 from=translated src=- shape=af6f8b24 vocab=8040ad84
-/
theorem betaDensity_integral {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    (∫ x : ℝ in 0..1, betaDensity a x) = 1 := by
  simpa only [pow_zero, one_mul, gammaMoment_zero ha] using
    betaDensity_moment_integral ha ha1 0

/--
@isnad1 id=le.4h2v.s5.6175e094b7c5 from=translated src=- shape=e9cad5d3 vocab=e46690b1
-/
theorem betaDensity_nonneg {a x : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ betaDensity a x := by
  unfold betaDensity betaKernel
  exact div_nonneg
    (mul_nonneg (Real.rpow_nonneg hx _) (Real.rpow_nonneg (sub_nonneg.mpr hx1) _))
    (mul_pos (Real.Gamma_pos_of_pos ha) (Real.Gamma_pos_of_pos (sub_pos.mpr ha1))).le

end Row12

