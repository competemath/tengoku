import Tengoku.Pi2Lean.Row12.Coefficient
import Tengoku.Pi2Lean.Row12.UniformMoment
import Tengoku.Seed.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Tengoku.Seed.Analysis.Analytic.ChangeOrigin
import Tengoku.Seed.Analysis.Calculus.FDeriv.Analytic
import Tengoku.Seed.Analysis.Calculus.SmoothSeries
import Tengoku.Seed.Analysis.Normed.Module.Connected

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms Row12.coefficient3_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.coefficient3_pos` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.coefficient3_nonneg` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.factorial_three_step` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.coefficient3_succ_mul` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.coefficient3_le_one` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.nativeEuler_summable` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.nativeF_eq_tsum` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.nativeSeries_radius` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.nativeF_analyticAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.nativeTerm_hasDerivAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.nativeDerivative_bound` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.nativeEuler_hasDerivAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.nativeEuler_succ_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.nativeEuler_cubic` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.nativeThetaIterate_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.nativeF_nativeODE` (it only prints; the queue checks the axioms of every declaration). -/

open scoped ENNReal NNReal

namespace Row12

/--
@isnad1 id=eq.0h0v.s3.f6f92a40d202 from=translated src=- shape=1ac31801 vocab=7372cf68
-/
theorem coefficient3_zero : coefficient3 0 = 1 := by
  norm_num [coefficient3]

/--
@isnad1 id=lt.0h1v.s3.0d7ba2068bcd from=translated src=- shape=b9369acb vocab=ba0c1814
-/
theorem coefficient3_pos (n : ℕ) : 0 < coefficient3 n := by
  unfold coefficient3
  positivity

/--
@isnad1 id=le.0h1v.s3.7082582eb2f4 from=translated src=- shape=b9369acb vocab=9412130f
-/
theorem coefficient3_nonneg (n : ℕ) : 0 ≤ coefficient3 n := (coefficient3_pos n).le

/--
@isnad1 id=eq.0h1v.s7.817a49a682f6 from=translated src=- shape=1fee208f vocab=3c69b864
-/
theorem factorial_three_step (n : ℕ) :
    (Nat.factorial (3 * (n + 1)) : ℝ) =
      (Nat.factorial (3 * n) : ℝ) * (3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2) *
        (3 * (n : ℝ) + 3) := by
  have hnat : Nat.factorial (3 * (n + 1)) =
      Nat.factorial (3 * n) * (3 * n + 1).ascFactorial 3 := by
    rw [Nat.factorial_mul_ascFactorial]
    congr 1
  have hcast : (Nat.factorial (3 * (n + 1)) : ℝ) =
      (Nat.factorial (3 * n) : ℝ) * ((3 * n + 1).ascFactorial 3 : ℝ) := by
    exact_mod_cast hnat
  rw [hcast]
  norm_num [Nat.ascFactorial]
  ring

/--
@isnad1 id=eq.0h1v.s7.41254c97c8b2 from=translated src=- shape=0f8c35ab vocab=19c672b3
-/
theorem coefficient3_succ_mul (n : ℕ) :
    ((n : ℝ) + 1) ^ 3 * coefficient3 (n + 1) =
      ((n : ℝ) + 1 / 6) * ((n : ℝ) + 1 / 2) * ((n : ℝ) + 5 / 6) * coefficient3 n := by
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hf3 : (Nat.factorial (3 * n) : ℝ) ≠ 0 := by positivity
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have h1 : 3 * (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : 3 * (n : ℝ) + 2 ≠ 0 := by positivity
  have h3 : 3 * (n : ℝ) + 3 ≠ 0 := by positivity
  unfold coefficient3
  rw [factorial_six_step, factorial_three_step, Nat.factorial_succ n, pow_succ]
  push_cast
  field_simp [hf, hf3, hn, h1, h2, h3]
  ring

/--
@isnad1 id=le.0h1v.s3.971a0635d403 from=translated src=- shape=a311c14d vocab=9412130f
-/
theorem coefficient3_le_one (n : ℕ) : coefficient3 n ≤ 1 := by
  induction n with
  | zero => rw [coefficient3_zero]
  | succ n ih =>
    have hn : (0 : ℝ) < ((n : ℝ) + 1) ^ 3 := by positivity
    have hp : ((n : ℝ) + 1 / 6) * ((n : ℝ) + 1 / 2) * ((n : ℝ) + 5 / 6) ≤
        ((n : ℝ) + 1) ^ 3 := by
      rw [pow_succ, pow_two]
      gcongr <;> norm_num
    have hb : ((n : ℝ) + 1) ^ 3 * coefficient3 (n + 1) ≤ ((n : ℝ) + 1) ^ 3 * 1 := by
      rw [coefficient3_succ_mul]
      exact mul_le_mul hp ih (coefficient3_nonneg n) (by positivity)
    exact (mul_le_mul_iff_right₀ hn).mp hb

section NativeFunction

variable {𝕜 : Type*} [RCLike 𝕜]

noncomputable def nativeEuler (k : ℕ) (q : 𝕜) : 𝕜 :=
  ∑' n : ℕ, (coefficient3 n : 𝕜) * (n : 𝕜) ^ k * q ^ n

noncomputable def nativeF (q : 𝕜) : 𝕜 := nativeEuler 0 q

noncomputable def nativeSeries (𝕜 : Type*) [RCLike 𝕜] : FormalMultilinearSeries 𝕜 𝕜 𝕜 :=
  FormalMultilinearSeries.ofScalars 𝕜 (fun n => (coefficient3 n : 𝕜))

/--
@isnad1 id=summable.1h3v.s7.a0e146bc41a0 from=translated src=- shape=cf44f60e vocab=f355dab7
-/
theorem nativeEuler_summable (k : ℕ) (q : 𝕜) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => (coefficient3 n : 𝕜) * (n : 𝕜) ^ k * q ^ n) := by
  have hr : ‖‖q‖‖ < 1 := by simpa only [Real.norm_eq_abs, abs_norm] using hq
  apply (summable_pow_mul_geometric_of_norm_lt_one k hr).of_norm_bounded
  intro n
  simp only [norm_mul, norm_pow, RCLike.norm_of_nonneg (coefficient3_nonneg n),
    RCLike.norm_natCast]
  calc
    coefficient3 n * (n : ℝ) ^ k * ‖q‖ ^ n ≤ 1 * (n : ℝ) ^ k * ‖q‖ ^ n := by
      gcongr
      exact coefficient3_le_one n
    _ = (n : ℝ) ^ k * ‖q‖ ^ n := by ring

/--
@isnad1 id=eq.0h2v.s6.90192fa32542 from=translated src=- shape=bdc1796d vocab=f855c0e7
-/
theorem nativeF_eq_tsum (q : 𝕜) : nativeF q = ∑' n : ℕ, (coefficient3 n : 𝕜) * q ^ n := by
  simp [nativeF, nativeEuler]

/--
@isnad1 id=le.0h1v.s6.36abd781a07e from=translated src=- shape=0c4f361f vocab=dc1a4e08
-/
theorem nativeSeries_radius : (1 : ℝ≥0∞) ≤ (nativeSeries 𝕜).radius := by
  apply (nativeSeries 𝕜).le_radius_of_bound (1 : ℝ) (r := (1 : ℝ≥0))
  intro n
  simp only [nativeSeries, FormalMultilinearSeries.ofScalars_norm, NNReal.coe_one,
    one_pow, mul_one, RCLike.norm_of_nonneg (coefficient3_nonneg n)]
  exact coefficient3_le_one n

/--
@isnad1 id=analytic.1h2v.s6.2b4e3b0616d0 from=translated src=- shape=8c2744f8 vocab=62836f63
-/
theorem nativeF_analyticAt (q : 𝕜) (hq : ‖q‖ < 1) : AnalyticAt 𝕜 nativeF q := by
  have hr : (0 : ℝ≥0∞) < (nativeSeries 𝕜).radius := lt_of_lt_of_le (by norm_num) nativeSeries_radius
  have hqr : ‖q‖ₑ < (nativeSeries 𝕜).radius := by
    apply lt_of_lt_of_le _ nativeSeries_radius
    have hnn : ‖q‖₊ < (1 : ℝ≥0) := by exact_mod_cast hq
    simpa only [ENNReal.coe_one] using (enorm_lt_coe).2 hnn
  have ha := ((nativeSeries 𝕜).hasFPowerSeriesOnBall hr).analyticAt_of_mem
    (show q ∈ Metric.eball (0 : 𝕜) (nativeSeries 𝕜).radius by simpa using hqr)
  have hfun : (nativeSeries 𝕜).sum = nativeF := by
    funext z
    rw [nativeF_eq_tsum]
    apply tsum_congr
    intro n
    simp [nativeSeries, smul_eq_mul, mul_comm]
  rw [hfun] at ha
  exact ha

/--
@isnad1 id=hasderiv.0h4v.s8.88b0219bbfd1 from=translated src=- shape=e80f6a33 vocab=3a4fd3b3
-/
theorem nativeTerm_hasDerivAt (k n : ℕ) (q : 𝕜) :
    HasDerivAt (fun q : 𝕜 => (coefficient3 n : 𝕜) * (n : 𝕜) ^ k * q ^ n)
      ((coefficient3 n : 𝕜) * (n : 𝕜) ^ (k + 1) * q ^ (n - 1)) q := by
  have hd := ((hasDerivAt_id q).pow n).const_mul ((coefficient3 n : 𝕜) * (n : 𝕜) ^ k)
  apply hd.congr_deriv
  simp only [id_eq]
  rw [pow_succ]
  ring

/--
@isnad1 id=le.2h5v.s8.c24cd71659b0 from=translated src=- shape=f55f08fe vocab=9b18c2a8
-/
theorem nativeDerivative_bound (k n : ℕ) {r : ℝ} (hr : 0 < r) (q : 𝕜) (hq : ‖q‖ ≤ r) :
    ‖(coefficient3 n : 𝕜) * (n : 𝕜) ^ (k + 1) * q ^ (n - 1)‖ ≤
      r⁻¹ * ((n : ℝ) ^ (k + 1) * r ^ n) := by
  simp only [norm_mul, norm_pow, RCLike.norm_of_nonneg (coefficient3_nonneg n),
    RCLike.norm_natCast]
  calc
    coefficient3 n * (n : ℝ) ^ (k + 1) * ‖q‖ ^ (n - 1) ≤
        1 * (n : ℝ) ^ (k + 1) * r ^ (n - 1) := by
      gcongr
      exact coefficient3_le_one n
    _ = r⁻¹ * ((n : ℝ) ^ (k + 1) * r ^ n) := by
      cases n with
      | zero => simp
      | succ n =>
        simp only [Nat.add_sub_cancel, pow_succ]
        field_simp

/--
@isnad1 id=hasderiv.1h3v.s8.2822b757c85b from=translated src=- shape=bd0adece vocab=756ef001
-/
theorem nativeEuler_hasDerivAt (k : ℕ) (q : 𝕜) (hq : ‖q‖ < 1) :
    HasDerivAt (nativeEuler k)
      (∑' n : ℕ, (coefficient3 n : 𝕜) * (n : 𝕜) ^ (k + 1) * q ^ (n - 1)) q := by
  let r : ℝ := (‖q‖ + 1) / 2
  have hr : 0 < r := by dsimp [r]; nlinarith [norm_nonneg q]
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hqr : ‖q‖ < r := by dsimp [r]; linarith
  have hgeom : Summable (fun n : ℕ => r⁻¹ * ((n : ℝ) ^ (k + 1) * r ^ n)) :=
    (summable_pow_mul_geometric_of_norm_lt_one (k + 1)
      (by simpa only [Real.norm_eq_abs, abs_of_pos hr] using hr1)).mul_left r⁻¹
  apply hasDerivAt_tsum_of_isPreconnected hgeom Metric.isOpen_ball Metric.isPreconnected_ball
    (t := Metric.ball (0 : 𝕜) r)
    (fun n y _ => nativeTerm_hasDerivAt k n y)
    (fun n y hy => nativeDerivative_bound k n hr y (by simpa using (Metric.mem_ball.mp hy).le))
    (y₀ := (0 : 𝕜))
  · simpa using hr
  · exact nativeEuler_summable k 0 (by simp)
  · simpa using hqr

/--
@isnad1 id=eq.1h3v.s7.f7d9922f68aa from=translated src=- shape=f6a938f2 vocab=1f9d30eb
-/
theorem nativeEuler_succ_eq (k : ℕ) (q : 𝕜) (hq : ‖q‖ < 1) :
    nativeEuler (k + 1) q = q * deriv (nativeEuler k) q := by
  rw [(nativeEuler_hasDerivAt k q hq).deriv, ← tsum_mul_left]
  unfold nativeEuler
  apply tsum_congr
  intro n
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.add_sub_cancel, pow_succ]
    ring

/--
@isnad1 id=eq.1h2v.s8.7a30e900e570 from=translated src=- shape=b76968b1 vocab=93f3607a
-/
theorem nativeEuler_cubic (q : 𝕜) (hq : ‖q‖ < 1) :
    nativeEuler 3 q = q * (nativeEuler 3 q + (3 / 2 : 𝕜) * nativeEuler 2 q +
      (23 / 36 : 𝕜) * nativeEuler 1 q + (5 / 72 : 𝕜) * nativeEuler 0 q) := by
  have h0 := nativeEuler_summable 0 q hq
  have h1 := nativeEuler_summable 1 q hq
  have h2 := nativeEuler_summable 2 q hq
  have h3 := nativeEuler_summable 3 q hq
  have hshift := h3.tsum_eq_zero_add
  simp only [Nat.cast_zero, zero_pow (by norm_num : 3 ≠ 0), mul_zero, zero_mul,
    zero_add] at hshift
  calc
    nativeEuler 3 q = ∑' n : ℕ, (coefficient3 (n + 1) : 𝕜) * (n + 1 : 𝕜) ^ 3 * q ^ (n + 1) := by
      simpa only [nativeEuler, Nat.cast_add, Nat.cast_one] using hshift
    _ = q * ∑' n : ℕ, (coefficient3 n : 𝕜) *
        ((n : 𝕜) + 1 / 6) * ((n : 𝕜) + 1 / 2) * ((n : 𝕜) + 5 / 6) * q ^ n := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      have hc : ((n : 𝕜) + 1) ^ 3 * (coefficient3 (n + 1) : 𝕜) =
          ((n : 𝕜) + 1 / 6) * ((n : 𝕜) + 1 / 2) * ((n : 𝕜) + 5 / 6) *
            (coefficient3 n : 𝕜) := by
        have hc := congrArg (algebraMap ℝ 𝕜) (coefficient3_succ_mul n)
        simpa only [map_mul, map_pow, map_add, map_div₀, map_one, map_ofNat, map_natCast] using hc
      calc
        _ = q * ((((n : 𝕜) + 1) ^ 3 * (coefficient3 (n + 1) : 𝕜)) * q ^ n) := by
          rw [pow_succ]
          ring
        _ = _ := by rw [hc]; ring
    _ = q * (nativeEuler 3 q + (3 / 2 : 𝕜) * nativeEuler 2 q +
        (23 / 36 : 𝕜) * nativeEuler 1 q + (5 / 72 : 𝕜) * nativeEuler 0 q) := by
      congr 1
      calc
        _ = ∑' n : ℕ, ((coefficient3 n : 𝕜) * (n : 𝕜) ^ 3 * q ^ n +
            (3 / 2 : 𝕜) * ((coefficient3 n : 𝕜) * (n : 𝕜) ^ 2 * q ^ n) +
            (23 / 36 : 𝕜) * ((coefficient3 n : 𝕜) * (n : 𝕜) ^ 1 * q ^ n) +
            (5 / 72 : 𝕜) * ((coefficient3 n : 𝕜) * (n : 𝕜) ^ 0 * q ^ n)) := by
          apply tsum_congr
          intro n
          ring
        _ = _ := by
          rw [((h3.add (h2.mul_left (3 / 2 : 𝕜))).add
              (h1.mul_left (23 / 36 : 𝕜))).tsum_add (h0.mul_left (5 / 72 : 𝕜)),
            (h3.add (h2.mul_left (3 / 2 : 𝕜))).tsum_add (h1.mul_left (23 / 36 : 𝕜)),
            h3.tsum_add (h2.mul_left (3 / 2 : 𝕜)),
            tsum_mul_left, tsum_mul_left, tsum_mul_left]
          rfl

noncomputable def nativeTheta (f : 𝕜 → 𝕜) (q : 𝕜) : 𝕜 := q * deriv f q

noncomputable def nativeThetaIterate : ℕ → 𝕜 → 𝕜
  | 0 => nativeF
  | k + 1 => nativeTheta (nativeThetaIterate k)

/--
@isnad1 id=eq.1h3v.s5.85ddf9c611f9 from=translated src=- shape=9b8197ad vocab=da05d03d
-/
theorem nativeThetaIterate_eq (k : ℕ) : ∀ q : 𝕜, ‖q‖ < 1 →
    nativeThetaIterate k q = nativeEuler k q := by
  induction k with
  | zero => intro q hq; rfl
  | succ k ih =>
    intro q hq
    have he : nativeThetaIterate k =ᶠ[nhds q] nativeEuler k := by
      have hb : Metric.ball (0 : 𝕜) 1 ∈ nhds q :=
        Metric.isOpen_ball.mem_nhds (by simpa using hq)
      filter_upwards [hb] with z hz
      exact ih z (by simpa using hz)
    change q * deriv (nativeThetaIterate k) q = nativeEuler (k + 1) q
    rw [he.deriv_eq]
    exact (nativeEuler_succ_eq k q hq).symm

/--
@isnad1 id=eq.1h2v.s8.aa15f86180e4 from=translated src=- shape=09f2eeac vocab=8e0aed4d
-/
theorem nativeF_nativeODE (q : 𝕜) (hq : ‖q‖ < 1) :
    nativeThetaIterate 3 q = q * (nativeThetaIterate 3 q +
      (3 / 2 : 𝕜) * nativeThetaIterate 2 q + (23 / 36 : 𝕜) * nativeThetaIterate 1 q +
      (5 / 72 : 𝕜) * nativeF q) := by
  rw [nativeThetaIterate_eq 3 q hq, nativeThetaIterate_eq 2 q hq,
    nativeThetaIterate_eq 1 q hq]
  exact nativeEuler_cubic q hq

end NativeFunction

end Row12

