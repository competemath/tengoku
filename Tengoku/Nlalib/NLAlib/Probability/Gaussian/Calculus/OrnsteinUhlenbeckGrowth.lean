import Tengoku.Nlalib.NLAlib.Probability.Gaussian.Calculus.OrnsteinUhlenbeckEntropy
import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.Real
import Tengoku.Nlalib.NLAlib.Probability.Gaussian.Calculus.PolynomialGrowthIntegrationByParts

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Polynomial-growth domains of the Mehler operator

Atlas: `ornstein-uhlenbeck`. Affine Gaussian moment bounds provide
integrability and polynomial spatial bounds for the existing Mehler
operator. Its commutation relation extends to C1 functions with
polynomially bounded values and derivatives.
Source: Bakry--Gentil--Ledoux 2014, §2.7.1; Ledoux, §5.1.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter

namespace NLAlib

/-- Polynomial weights of an affine map have an integrable Gaussian
majorant. Source: elementary absolute-value inequalities and Gaussian
moments. Atlas: `ornstein-uhlenbeck`.
@isnad1 id=le.0h4v.s7.d79c26a4e8c3 from=translated src=- shape=77e75563 vocab=50773ea0
-/
theorem one_add_abs_add_mul_pow_le (a b y : ℝ) (d : ℕ) :
    (1 + |a + b * y|) ^ d ≤ (1 + |a| + |b|) ^ d * (1 + |y|) ^ d := by
  have h1 : 1 + |a + b * y| ≤ (1 + |a| + |b|) * (1 + |y|) := by
    have h := abs_add_le a (b * y)
    rw [abs_mul] at h
    nlinarith [abs_nonneg a, abs_nonneg b, abs_nonneg y]
  simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) h1 d

/-- Measurable polynomial-growth functions remain integrable after every
affine change of a Gaussian variable. Source: Gaussian moment finiteness.
Atlas: `ornstein-uhlenbeck`.
@isnad1 id=integrab.2h5v.s6.e1b456480fd9 from=translated src=- shape=e75117bd vocab=0839282b
-/
theorem integrable_comp_add_mul_of_polynomial_growth {f : ℝ → ℝ} (hf : Measurable f)
    (C : ℝ) (d : ℕ) (hValue : ∀ x, |f x| ≤ C * (1 + |x|) ^ d) (a b : ℝ) :
    Integrable (fun y => f (a + b * y)) (gaussianReal 0 1) := by
  have hC : 0 ≤ C := by
    have h := hValue 0
    simp only [abs_zero, add_zero, one_pow, mul_one] at h
    exact (abs_nonneg _).trans h
  apply integrable_gaussianReal_of_polynomial_growth (hf.comp (by fun_prop)).aemeasurable
    (C * (1 + |a| + |b|) ^ d) d
  intro y
  exact (hValue _).trans (by
    have h := mul_le_mul_of_nonneg_left (one_add_abs_add_mul_pow_le a b y d) hC
    simpa only [mul_assoc] using h)

/-- A Mehler affine map with coefficients bounded by one separates its
polynomial weight into a spatial and a noise weight.
Source: elementary absolute-value inequalities.
Atlas: `ornstein-uhlenbeck`.
@isnad1 id=le.2h5v.s7.d895f69cfc51 from=translated src=- shape=0c909fb0 vocab=50773ea0
-/
theorem one_add_abs_mul_add_mul_pow_le (a b x y : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) (d : ℕ) :
    (1 + |a * x + b * y|) ^ d ≤ (1 + |x|) ^ d * (1 + |y|) ^ d := by
  have h1 : |a * x + b * y| ≤ |x| + |y| := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have hx := mul_le_mul_of_nonneg_right ha (abs_nonneg x)
    have hy := mul_le_mul_of_nonneg_right hb (abs_nonneg y)
    nlinarith
  have h2 : 1 + |a * x + b * y| ≤ (1 + |x|) * (1 + |y|) := by
    nlinarith [abs_nonneg x, abs_nonneg y]
  simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) h2 d

/-- The first Mehler coefficient `e^{-t}` has absolute value at most one for `t ≥ 0`.
Bakry–Gentil–Ledoux 2014, §2.7.1.
@isnad1 id=le.1h1v.s4.61ff62d74994 from=translated src=- shape=2562438e vocab=1f83dadd
-/
theorem abs_exp_neg_le_one {t : ℝ} (ht : 0 ≤ t) : |Real.exp (-t)| ≤ 1 := by
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.2 (by linarith)

/-- The second Mehler coefficient `√(1 - e^{-2t})` has absolute value at most one for `t ≥ 0`.
Bakry–Gentil–Ledoux 2014, §2.7.1.
@isnad1 id=le.1h1v.s5.7fd902d484b1 from=translated src=- shape=d94410a2 vocab=0b0504a3
-/
theorem abs_sqrt_one_sub_exp_neg_le_one {t : ℝ} (ht : 0 ≤ t) :
    |Real.sqrt (1 - Real.exp (-(2 * t)))| ≤ 1 := by
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  have he : Real.exp (-(2 * t)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hs := Real.sq_sqrt (by linarith : 0 ≤ 1 - Real.exp (-(2 * t)))
  nlinarith [Real.sqrt_nonneg (1 - Real.exp (-(2 * t))), Real.exp_pos (-(2 * t))]

/-- A polynomial spatial majorant for the Mehler conditional expectation,
with a literal finite Gaussian moment rather than a moment hypothesis.
Source: Mehler's formula and Gaussian moment finiteness.
Atlas: `ornstein-uhlenbeck`.
@isnad1 id=le.3h5v.s7.8dcbfdd2f1c0 from=translated src=- shape=70d1479b vocab=cef96ff4
-/
theorem abs_ornsteinUhlenbeck_le_polynomial {f : ℝ → ℝ} (hf : Measurable f)
    (C : ℝ) (d : ℕ) (hValue : ∀ x, |f x| ≤ C * (1 + |x|) ^ d)
    (t x : ℝ) (ht : 0 ≤ t) :
    |ornsteinUhlenbeck t f x| ≤
      C * (∫ y : ℝ, (1 + |y|) ^ d ∂(gaussianReal 0 1)) * (1 + |x|) ^ d := by
  have hC : 0 ≤ C := by
    have h := hValue 0
    simp only [abs_zero, add_zero, one_pow, mul_one] at h
    exact (abs_nonneg _).trans h
  have ha := abs_exp_neg_le_one ht
  have hb := abs_sqrt_one_sub_exp_neg_le_one ht
  unfold ornsteinUhlenbeck
  have hdom : Integrable (fun y : ℝ => C * (1 + |x|) ^ d * (1 + |y|) ^ d)
      (gaussianReal 0 1) := (integrable_one_add_abs_pow_gaussianReal d).const_mul _
  have hi := integrable_comp_add_mul_of_polynomial_growth hf C d hValue
    (Real.exp (-t) * x) (Real.sqrt (1 - Real.exp (-(2 * t))))
  have h := abs_integral_le_integral_abs |>.trans (integral_mono hi.abs hdom (fun y => by
    exact (hValue _).trans (by
      have h := mul_le_mul_of_nonneg_left
        (one_add_abs_mul_add_mul_pow_le _ _ x y ha hb d) hC
      simpa only [mul_assoc] using h)))
  rw [integral_const_mul] at h
  nlinarith

/-- Positive lower bounds are preserved by the Mehler operator on its
polynomial-growth domain; section integrability is derived.
Source: positivity and mass preservation of conditional expectation.
Atlas: `ornstein-uhlenbeck`.
@isnad1 id=le.3h6v.s6.1df7a6bbbe85 from=translated src=- shape=468eff86 vocab=7fb571b4
-/
theorem le_ornsteinUhlenbeck_of_polynomial_growth {f : ℝ → ℝ} (hf : Measurable f)
    (C : ℝ) (d : ℕ) (hValue : ∀ x, |f x| ≤ C * (1 + |x|) ^ d)
    (δ : ℝ) (hlow : ∀ x, δ ≤ f x) (t x : ℝ) : δ ≤ ornsteinUhlenbeck t f x := by
  have hi := integrable_comp_add_mul_of_polynomial_growth hf C d hValue
    (Real.exp (-t) * x) (Real.sqrt (1 - Real.exp (-(2 * t))))
  have h := integral_mono (integrable_const δ) hi (fun y => hlow _)
  simpa only [ornsteinUhlenbeck, integral_const, probReal_univ, one_smul] using h

/-- The joint time/space Mehler conditional expectation is measurable.
No integrability claim is hidden in this statement.
Source: measurable parameter integrals. Atlas: `ornstein-uhlenbeck`.
@isnad1 id=measurab.1h1v.s5.9d855edbc0b4 from=translated src=- shape=024d884b vocab=833a5040
-/
theorem measurable_ornsteinUhlenbeck_joint {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (fun p : ℝ × ℝ => ornsteinUhlenbeck p.1 f p.2) := by
  exact (StronglyMeasurable.integral_prod_right'
    (f := fun p : (ℝ × ℝ) × ℝ => f (Real.exp (-p.1.1) * p.1.2 +
      Real.sqrt (1 - Real.exp (-(2 * p.1.1))) * p.2))
    (hf.comp (by fun_prop)).stronglyMeasurable).measurable

/-- Spatial commutation for C1 functions with polynomially bounded values
and derivatives. Source: Bakry--Gentil--Ledoux, §2.7.1. The proof extends
NLAlib's bounded-derivative argument with Gaussian polynomial dominators.
Atlas: `ornstein-uhlenbeck`.
atlas: ornstein-uhlenbeck
@isnad1 id=hasderiv.3h5v.s8.ea0aac1ba00c from=translated src=- shape=8e3c7a40 vocab=b0c3cd05
-/
theorem hasDerivAt_ornsteinUhlenbeck_of_polynomial_growth
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (C : ℝ) (d : ℕ)
    (hValue : ∀ z, |f z| ≤ C * (1 + |z|) ^ d)
    (hDeriv : ∀ z, |deriv f z| ≤ C * (1 + |z|) ^ d) (t x : ℝ) :
    HasDerivAt (ornsteinUhlenbeck t f)
      (Real.exp (-t) * ornsteinUhlenbeck t (deriv f) x) x := by
  let a := Real.exp (-t)
  let b := Real.sqrt (1 - Real.exp (-(2 * t)))
  let K := 1 + |a| * (|x| + 1) + |b|
  have hC : 0 ≤ C := by
    have h := hValue 0
    simp only [abs_zero, add_zero, one_pow, mul_one] at h
    exact (abs_nonneg _).trans h
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hdc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  change HasDerivAt (fun z => ∫ y, f (a * z + b * y) ∂(gaussianReal 0 1))
    (a * ∫ y, deriv f (a * x + b * y) ∂(gaussianReal 0 1)) x
  rw [← integral_const_mul]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (F := fun z y => f (a * z + b * y))
    (F' := fun z y => a * deriv f (a * z + b * y)) (x₀ := x)
    (bound := fun y => |a| * C * K ^ d * (1 + |y|) ^ d)
    (Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1)) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall fun z => (hf.continuous.comp (by fun_prop)).aestronglyMeasurable
  · exact integrable_comp_add_mul_of_polynomial_growth hf.continuous.measurable C d hValue (a * x) b
  · exact ((hdc.comp (by fun_prop)).const_mul a).aestronglyMeasurable
  · refine Eventually.of_forall fun y z hz => ?_
    have hz1 : |z| ≤ |x| + 1 := by
      have hz' : |z - x| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hz
      have h := abs_add_le (z - x) x
      have he : z - x + x = z := by ring
      rw [he] at h
      linarith
    have hbase : 1 + |a * z + b * y| ≤ K * (1 + |y|) := by
      have h := abs_add_le (a * z) (b * y)
      rw [abs_mul, abs_mul] at h
      have hzbound := mul_le_mul_of_nonneg_left hz1 (abs_nonneg a)
      dsimp [K]
      have hp := mul_nonneg (mul_nonneg (abs_nonneg a) (by positivity : 0 ≤ |x| + 1))
        (abs_nonneg y)
      nlinarith [abs_nonneg a, abs_nonneg b, abs_nonneg x, abs_nonneg y]
    have hpow := pow_le_pow_left₀ (by positivity) hbase d
    rw [mul_pow] at hpow
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul_of_nonneg_left (hDeriv _) (abs_nonneg a)).trans (by
      have h := mul_le_mul_of_nonneg_left hpow (mul_nonneg (abs_nonneg a) hC)
      simpa only [mul_assoc] using h)
  · exact (integrable_one_add_abs_pow_gaussianReal d).const_mul _
  · refine Eventually.of_forall fun y z _ => ?_
    have hlin : HasDerivAt (fun z => a * z + b * y) a z := by
      simpa using ((hasDerivAt_id z).const_mul a).add_const (b * y)
    have h := (hfd _).hasDerivAt.comp z hlin
    simpa only [Function.comp_def, mul_comm] using h

/-- Polynomially dominated functions pass pointwise limits through the
Mehler conditional expectation. Every noise-section dominator has a
finite Gaussian moment. Source: dominated convergence.
Atlas: `ornstein-uhlenbeck`.
@isnad1 id=tendsto.3h6v.s7.f9338370a637 from=translated src=- shape=9f293ea2 vocab=b44ec2a1
-/
theorem tendsto_ornsteinUhlenbeck_of_polynomial_bound (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hFm : ∀ n, Measurable (F n)) (C : ℝ) (d : ℕ)
    (hBound : ∀ n y, |F n y| ≤ C * (1 + |y|) ^ d)
    (hlim : ∀ y, Tendsto (fun n => F n y) atTop (nhds (f y))) (t x : ℝ) :
    Tendsto (fun n => ornsteinUhlenbeck t (F n) x) atTop
      (nhds (ornsteinUhlenbeck t f x)) := by
  have hC : 0 ≤ C := by
    have h := hBound 0 0
    simp only [abs_zero, add_zero, one_pow, mul_one] at h
    exact (abs_nonneg _).trans h
  unfold ornsteinUhlenbeck
  refine tendsto_integral_of_dominated_convergence
    (fun y => C * (1 + |Real.exp (-t) * x| +
      |Real.sqrt (1 - Real.exp (-(2 * t)))|) ^ d * (1 + |y|) ^ d)
    (fun n => ((hFm n).comp (by fun_prop)).aestronglyMeasurable)
    ((integrable_one_add_abs_pow_gaussianReal d).const_mul _)
    (fun n => ae_of_all _ fun y => ?_) (ae_of_all _ fun y => hlim _)
  rw [Real.norm_eq_abs]
  exact (hBound n _).trans (by
    have h := mul_le_mul_of_nonneg_left (one_add_abs_add_mul_pow_le
      (Real.exp (-t) * x) (Real.sqrt (1 - Real.exp (-(2 * t)))) y d) hC
    simpa only [mul_assoc] using h)

/-- At positive times, a continuous polynomial-growth function has a
continuous Mehler conditional expectation as a function of time.
Source: parameter-integral dominated convergence.
Atlas: `ornstein-uhlenbeck`.
@isnad1 id=continuo.3h5v.s6.61d18cb4ca2a from=translated src=- shape=a934cdf8 vocab=73ce09e5
-/
theorem continuousAt_ornsteinUhlenbeck_time_of_polynomial_growth {f : ℝ → ℝ}
    (hf : Continuous f) (C : ℝ) (d : ℕ)
    (hValue : ∀ y, |f y| ≤ C * (1 + |y|) ^ d) (t x : ℝ) (ht : 0 < t) :
    ContinuousAt (fun s => ornsteinUhlenbeck s f x) t := by
  have hC : 0 ≤ C := by
    have h := hValue 0
    simp only [abs_zero, add_zero, one_pow, mul_one] at h
    exact (abs_nonneg _).trans h
  change Tendsto (fun s => ornsteinUhlenbeck s f x) (nhds t)
    (nhds (ornsteinUhlenbeck t f x))
  unfold ornsteinUhlenbeck
  refine tendsto_integral_filter_of_dominated_convergence
    (fun y => C * (1 + |x|) ^ d * (1 + |y|) ^ d)
    (Eventually.of_forall fun s => (hf.measurable.comp (by fun_prop)).aestronglyMeasurable)
    ?_ ((integrable_one_add_abs_pow_gaussianReal d).const_mul _)
    (ae_of_all _ fun y => (hf.comp (by fun_prop)).tendsto t)
  have hnear : ∀ᶠ s in nhds t, 0 < s := isOpen_Ioi.mem_nhds ht
  filter_upwards [hnear] with s hs
  exact ae_of_all _ fun y => by
    rw [Real.norm_eq_abs]
    have ha := abs_exp_neg_le_one hs.le
    have hb := abs_sqrt_one_sub_exp_neg_le_one hs.le
    exact (hValue _).trans (by
      have h := mul_le_mul_of_nonneg_left
        (one_add_abs_mul_add_mul_pow_le _ _ x y ha hb d) hC
      simpa only [mul_assoc] using h)

/-- Fisher integrand of the Mehler operator, written using its explicit
commutation relation. The next bridge identifies it with the
spatial derivative on the polynomial-growth domain.
Source: Bakry--Gentil--Ledoux, §5.7. Atlas: `ornstein-uhlenbeck`.
atlas: ornstein-uhlenbeck-/
def ornsteinUhlenbeckFisherIntegrand (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (Real.exp (-t) * ornsteinUhlenbeck t (deriv f) x) ^ 2 / ornsteinUhlenbeck t f x

/-- The commutation form of the Fisher integrand equals its
derivative form. Source: the proved polynomial-growth commutation
relation. Atlas: `ornstein-uhlenbeck`.
@isnad1 id=eq.3h5v.s7.c0b03e5fe842 from=translated src=- shape=52d4dab9 vocab=0fb532c6
-/
theorem ornsteinUhlenbeckFisherIntegrand_eq (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (C : ℝ) (d : ℕ) (hValue : ∀ y, |f y| ≤ C * (1 + |y|) ^ d)
    (hDeriv : ∀ y, |deriv f y| ≤ C * (1 + |y|) ^ d) (t x : ℝ) :
    ornsteinUhlenbeckFisherIntegrand t f x =
      deriv (ornsteinUhlenbeck t f) x ^ 2 / ornsteinUhlenbeck t f x := by
  rw [(hasDerivAt_ornsteinUhlenbeck_of_polynomial_growth f hf C d hValue hDeriv t x).deriv]
  rfl

/-- The joint Fisher integrand is measurable. Source: measurable
parameter integrals and arithmetic operations.
Atlas: `ornstein-uhlenbeck`.
@isnad1 id=measurab.1h1v.s5.267f1ca059ef from=translated src=- shape=024d884b vocab=3911f81d
-/
theorem measurable_ornsteinUhlenbeckFisherIntegrand_joint {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (fun p : ℝ × ℝ => ornsteinUhlenbeckFisherIntegrand p.1 f p.2) := by
  have ha : Measurable (fun p : ℝ × ℝ => Real.exp (-p.1)) := by fun_prop
  exact ((ha.mul (measurable_ornsteinUhlenbeck_joint (measurable_deriv f))).pow_const 2).div
    (measurable_ornsteinUhlenbeck_joint hf)

/-- An explicit Gaussian-polynomial dominator of Fisher information.
The positive lower bound controls the denominator, and the literal
Gaussian moment is finite by the moment theorem.
Source: Mehler commutation and Gaussian moments.
Atlas: `ornstein-uhlenbeck`.
@isnad1 id=le.6h7v.s8.33d2b1e995f0 from=translated src=- shape=1dc37684 vocab=3ae1630f
-/
theorem abs_ornsteinUhlenbeckFisherIntegrand_le {f : ℝ → ℝ} (hf : Measurable f)
    (C D : ℝ) (d : ℕ) (hValue : ∀ y, |f y| ≤ C * (1 + |y|) ^ d)
    (hDeriv : ∀ y, |deriv f y| ≤ D * (1 + |y|) ^ d)
    (δ : ℝ) (hδ : 0 < δ) (hlow : ∀ y, δ ≤ f y) (t x : ℝ) (ht : 0 ≤ t) :
    |ornsteinUhlenbeckFisherIntegrand t f x| ≤
      (D * (∫ y : ℝ, (1 + |y|) ^ d ∂(gaussianReal 0 1))) ^ 2 / δ * (1 + |x|) ^ (2 * d) := by
  have hu := le_ornsteinUhlenbeck_of_polynomial_growth hf C d hValue δ hlow t x
  have hup : 0 < ornsteinUhlenbeck t f x := lt_of_lt_of_le hδ hu
  have hb := abs_ornsteinUhlenbeck_le_polynomial (measurable_deriv f) D d hDeriv t x ht
  have ha : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hnum : |Real.exp (-t) * ornsteinUhlenbeck t (deriv f) x| ≤
      D * (∫ y : ℝ, (1 + |y|) ^ d ∂(gaussianReal 0 1)) * (1 + |x|) ^ d := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have h := mul_le_mul ha hb (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using h
  have hs : (Real.exp (-t) * ornsteinUhlenbeck t (deriv f) x) ^ 2 ≤
      (D * (∫ y : ℝ, (1 + |y|) ^ d ∂(gaussianReal 0 1))) ^ 2 * (1 + |x|) ^ (2 * d) := by
    simpa only [sq_abs, mul_pow, ← pow_mul, Nat.mul_comm] using
      pow_le_pow_left₀ (abs_nonneg _) hnum 2
  unfold ornsteinUhlenbeckFisherIntegrand
  rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hup.le)]
  apply (div_le_iff₀ hup).2
  calc
    _ ≤ (D * (∫ y : ℝ, (1 + |y|) ^ d ∂(gaussianReal 0 1))) ^ 2 *
        (1 + |x|) ^ (2 * d) := hs
    _ = ((D * (∫ y : ℝ, (1 + |y|) ^ d ∂(gaussianReal 0 1))) ^ 2 / δ *
        (1 + |x|) ^ (2 * d)) * δ := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hu (by positivity)

/-- Fisher information is integrable on the positive polynomial-growth
domain; no moment-integrability certificates are assumed.
Source: the explicit polynomial majorant above and Gaussian moments.
Atlas: `ornstein-uhlenbeck`.
@isnad1 id=integrab.6h6v.s7.6d52441d49da from=translated src=- shape=1937faaf vocab=084b93bb
-/
theorem integrable_ornsteinUhlenbeckFisherIntegrand {f : ℝ → ℝ} (hf : Measurable f)
    (C D : ℝ) (d : ℕ) (hValue : ∀ y, |f y| ≤ C * (1 + |y|) ^ d)
    (hDeriv : ∀ y, |deriv f y| ≤ D * (1 + |y|) ^ d)
    (δ : ℝ) (hδ : 0 < δ) (hlow : ∀ y, δ ≤ f y) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (ornsteinUhlenbeckFisherIntegrand t f) (gaussianReal 0 1) := by
  apply integrable_gaussianReal_of_polynomial_growth
    ((measurable_ornsteinUhlenbeckFisherIntegrand_joint hf).comp
      (measurable_const.prodMk measurable_id)).aemeasurable
    ((D * (∫ y : ℝ, (1 + |y|) ^ d ∂(gaussianReal 0 1))) ^ 2 / δ) (2 * d)
  intro x
  exact abs_ornsteinUhlenbeckFisherIntegrand_le hf C D d hValue hDeriv δ hδ hlow t x ht

/-- The integrated Fisher information is measurable in time. Source:
measurable parameter integrals. Atlas: `ornstein-uhlenbeck`.
@isnad1 id=measurab.1h1v.s5.c135156d8ab1 from=translated src=- shape=5a1a0b93 vocab=2f3da3ed
-/
theorem measurable_integral_ornsteinUhlenbeckFisherIntegrand {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (fun t => ∫ x, ornsteinUhlenbeckFisherIntegrand t f x ∂(gaussianReal 0 1)) := by
  exact (StronglyMeasurable.integral_prod_right'
    (f := fun p : ℝ × ℝ => ornsteinUhlenbeckFisherIntegrand p.1 f p.2)
    (measurable_ornsteinUhlenbeckFisherIntegrand_joint hf).stronglyMeasurable).measurable

/-- The Fisher information is continuous at positive times on the C1
polynomial-growth domain. Source: two Gaussian dominated-convergence
steps, using the positive lower bound. Atlas: `ornstein-uhlenbeck`.
@isnad1 id=continuo.6h6v.s8.cbc993be02c8 from=translated src=- shape=3de05752 vocab=ac840f4e
-/
theorem continuousAt_integral_ornsteinUhlenbeckFisherIntegrand (f : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) (C D : ℝ) (d : ℕ)
    (hValue : ∀ y, |f y| ≤ C * (1 + |y|) ^ d)
    (hDeriv : ∀ y, |deriv f y| ≤ D * (1 + |y|) ^ d)
    (δ : ℝ) (hδ : 0 < δ) (hlow : ∀ y, δ ≤ f y) (t : ℝ) (ht : 0 < t) :
    ContinuousAt (fun s => ∫ x, ornsteinUhlenbeckFisherIntegrand s f x ∂(gaussianReal 0 1)) t := by
  have hmeas := measurable_ornsteinUhlenbeckFisherIntegrand_joint hf.continuous.measurable
  change Tendsto (fun s => ∫ x, ornsteinUhlenbeckFisherIntegrand s f x ∂(gaussianReal 0 1))
    (nhds t) (nhds (∫ x, ornsteinUhlenbeckFisherIntegrand t f x ∂(gaussianReal 0 1)))
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x => (D * (∫ y : ℝ, (1 + |y|) ^ d ∂(gaussianReal 0 1))) ^ 2 / δ *
      (1 + |x|) ^ (2 * d))
    (Eventually.of_forall fun s => (hmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    ?_ ((integrable_one_add_abs_pow_gaussianReal (2 * d)).const_mul _) ?_
  · have hnear : ∀ᶠ s in nhds t, 0 < s := isOpen_Ioi.mem_nhds ht
    filter_upwards [hnear] with s hs
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      exact abs_ornsteinUhlenbeckFisherIntegrand_le hf.continuous.measurable
        C D d hValue hDeriv δ hδ hlow s x hs.le
  · refine ae_of_all _ fun x => ?_
    have h1 := continuousAt_ornsteinUhlenbeck_time_of_polynomial_growth
      hf.continuous C d hValue t x ht
    have h2 := continuousAt_ornsteinUhlenbeck_time_of_polynomial_growth
      (hf.continuous_deriv le_rfl) D d hDeriv t x ht
    have hp : ornsteinUhlenbeck t f x ≠ 0 :=
      (lt_of_lt_of_le hδ (le_ornsteinUhlenbeck_of_polynomial_growth
        hf.continuous.measurable C d hValue δ hlow t x)).ne'
    exact (((Real.continuous_exp.comp continuous_id.neg).continuousAt.mul h2).pow 2).div h1 hp

/-- The spatial entropy integrand of the Mehler expectation is integrable
for positive polynomial-growth functions. Source: Gaussian moments and
`|u log u| ≤ u²+1`. Atlas: `ornstein-uhlenbeck`.
@isnad1 id=integrab.5h5v.s7.fbe828b3f17d from=translated src=- shape=4e1eb4ab vocab=e79bc52d
-/
theorem integrable_ornsteinUhlenbeck_mul_log_of_polynomial_growth {f : ℝ → ℝ}
    (hf : Measurable f) (C : ℝ) (d : ℕ) (hValue : ∀ y, |f y| ≤ C * (1 + |y|) ^ d)
    (δ : ℝ) (hδ : 0 < δ) (hlow : ∀ y, δ ≤ f y) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun x => ornsteinUhlenbeck t f x * Real.log (ornsteinUhlenbeck t f x))
      (gaussianReal 0 1) := by
  have hm : Measurable (ornsteinUhlenbeck t f) :=
    (measurable_ornsteinUhlenbeck_joint hf).comp (measurable_const.prodMk measurable_id)
  apply integrable_gaussianReal_of_polynomial_growth (hm.mul hm.log).aemeasurable
    ((C * (∫ y : ℝ, (1 + |y|) ^ d ∂(gaussianReal 0 1))) ^ 2 + 1) (2 * d)
  intro x
  have hu : 0 ≤ ornsteinUhlenbeck t f x :=
    hδ.le.trans (le_ornsteinUhlenbeck_of_polynomial_growth hf C d hValue δ hlow t x)
  have h := abs_ornsteinUhlenbeck_le_polynomial hf C d hValue t x ht
  have hs : ornsteinUhlenbeck t f x ^ 2 ≤
      (C * (∫ y : ℝ, (1 + |y|) ^ d ∂(gaussianReal 0 1))) ^ 2 * (1 + |x|) ^ (2 * d) := by
    simpa only [sq_abs, mul_pow, ← pow_mul, Nat.mul_comm] using
      pow_le_pow_left₀ (abs_nonneg _) h 2
  have hW : (1 : ℝ) ≤ (1 + |x|) ^ (2 * d) := one_le_pow₀ (by linarith [abs_nonneg x])
  have hlog := abs_mul_log_le_sq_add_one (ornsteinUhlenbeck t f x) hu
  change |ornsteinUhlenbeck t f x * Real.log (ornsteinUhlenbeck t f x)| ≤
    ((C * (∫ y : ℝ, (1 + |y|) ^ d ∂(gaussianReal 0 1))) ^ 2 + 1) * (1 + |x|) ^ (2 * d)
  nlinarith

/-- A time-uniform finite bound on integrated Fisher information for
nonnegative times. All moments are Gaussian integrals, and
their finiteness is derived. Source: the Gaussian polynomial dominator.
Atlas: `ornstein-uhlenbeck`.
@isnad1 id=le.6h6v.s8.ac0505d74002 from=translated src=- shape=2a5591d4 vocab=3ae1630f
-/
theorem abs_integral_ornsteinUhlenbeckFisherIntegrand_le {f : ℝ → ℝ} (hf : Measurable f)
    (C D : ℝ) (d : ℕ) (hValue : ∀ y, |f y| ≤ C * (1 + |y|) ^ d)
    (hDeriv : ∀ y, |deriv f y| ≤ D * (1 + |y|) ^ d)
    (δ : ℝ) (hδ : 0 < δ) (hlow : ∀ y, δ ≤ f y) (t : ℝ) (ht : 0 ≤ t) :
    |∫ x, ornsteinUhlenbeckFisherIntegrand t f x ∂(gaussianReal 0 1)| ≤
      (D * (∫ y : ℝ, (1 + |y|) ^ d ∂(gaussianReal 0 1))) ^ 2 / δ *
        (∫ x : ℝ, (1 + |x|) ^ (2 * d) ∂(gaussianReal 0 1)) := by
  have hi := integrable_ornsteinUhlenbeckFisherIntegrand hf C D d hValue hDeriv δ hδ hlow t ht
  have hdom := (integrable_one_add_abs_pow_gaussianReal (2 * d)).const_mul
    ((D * (∫ y : ℝ, (1 + |y|) ^ d ∂(gaussianReal 0 1))) ^ 2 / δ)
  have h := abs_integral_le_integral_abs |>.trans (integral_mono hi.abs hdom
    (fun x => abs_ornsteinUhlenbeckFisherIntegrand_le hf C D d hValue hDeriv δ hδ hlow t x ht))
  rw [integral_const_mul] at h
  exact h

end NLAlib
