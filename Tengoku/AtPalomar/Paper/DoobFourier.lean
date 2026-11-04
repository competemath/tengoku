module

public import Tengoku.AtPalomar.Paper.StateDiffusion
public import Tengoku.AtPalomar.Paper.Hyperbolic
public import Tengoku.Seed.Analysis.Calculus.ContDiff.Operations
public import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# Explicit Fourier solutions for the cosh Doob generator

The real and imaginary Fourier modes have elementary closed forms. Their
actual time and first/second spatial derivatives satisfy the backward equation
for the generator `(1/2)∂xx + tanh(x)∂x` after the physical β² time rescaling.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ContDiff

namespace Paper

/--
@isnad1 id=continuo.0h0v.s3.f7ac065c86b1 from=translated src=- shape=e3d48bcb vocab=3a14495e
-/
@[fun_prop] theorem doobFourier_continuous_sech : Continuous sech := by
  unfold sech
  exact continuous_const.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')

/-- Real Fourier mode of the cosh transform at remaining variance `ell`.-/
def doobFourierCos (ξ ell x : ℝ) : ℝ :=
  Real.exp (-(ξ ^ 2 * ell) / 2) *
    (Real.cos (ξ * x) * Real.cos (ξ * ell) -
      Real.tanh x * Real.sin (ξ * x) * Real.sin (ξ * ell))

/-- Imaginary Fourier mode of the cosh transform.-/
def doobFourierSin (ξ ell x : ℝ) : ℝ :=
  Real.exp (-(ξ ^ 2 * ell) / 2) *
    (Real.sin (ξ * x) * Real.cos (ξ * ell) +
      Real.tanh x * Real.cos (ξ * x) * Real.sin (ξ * ell))

def doobFourierCosDx (ξ ell x : ℝ) : ℝ :=
  Real.exp (-(ξ ^ 2 * ell) / 2) *
    (-ξ * Real.sin (ξ * x) * Real.cos (ξ * ell) -
      (sech x ^ 2 * Real.sin (ξ * x) + ξ * Real.tanh x * Real.cos (ξ * x)) * Real.sin (ξ * ell))

def doobFourierSinDx (ξ ell x : ℝ) : ℝ :=
  Real.exp (-(ξ ^ 2 * ell) / 2) *
    (ξ * Real.cos (ξ * x) * Real.cos (ξ * ell) +
      (sech x ^ 2 * Real.cos (ξ * x) - ξ * Real.tanh x * Real.sin (ξ * x)) * Real.sin (ξ * ell))

def doobFourierCosDxx (ξ ell x : ℝ) : ℝ :=
  Real.exp (-(ξ ^ 2 * ell) / 2) *
    (-ξ ^ 2 * Real.cos (ξ * x) * Real.cos (ξ * ell) -
      ((-2 * Real.tanh x * sech x ^ 2 - ξ ^ 2 * Real.tanh x) * Real.sin (ξ * x) +
        2 * ξ * sech x ^ 2 * Real.cos (ξ * x)) * Real.sin (ξ * ell))

def doobFourierSinDxx (ξ ell x : ℝ) : ℝ :=
  Real.exp (-(ξ ^ 2 * ell) / 2) *
    (-ξ ^ 2 * Real.sin (ξ * x) * Real.cos (ξ * ell) +
      ((-2 * Real.tanh x * sech x ^ 2 - ξ ^ 2 * Real.tanh x) * Real.cos (ξ * x) -
        2 * ξ * sech x ^ 2 * Real.sin (ξ * x)) * Real.sin (ξ * ell))

def doobFourierCosDell (ξ ell x : ℝ) : ℝ :=
  Real.exp (-(ξ ^ 2 * ell) / 2) *
    (-(ξ ^ 2) / 2 * (Real.cos (ξ * x) * Real.cos (ξ * ell) -
      Real.tanh x * Real.sin (ξ * x) * Real.sin (ξ * ell)) -
      ξ * Real.cos (ξ * x) * Real.sin (ξ * ell) -
      ξ * Real.tanh x * Real.sin (ξ * x) * Real.cos (ξ * ell))

def doobFourierSinDell (ξ ell x : ℝ) : ℝ :=
  Real.exp (-(ξ ^ 2 * ell) / 2) *
    (-(ξ ^ 2) / 2 * (Real.sin (ξ * x) * Real.cos (ξ * ell) +
      Real.tanh x * Real.cos (ξ * x) * Real.sin (ξ * ell)) -
      ξ * Real.sin (ξ * x) * Real.sin (ξ * ell) +
      ξ * Real.tanh x * Real.cos (ξ * x) * Real.cos (ξ * ell))

/-- Exact generator cancellation for the real Fourier mode.
@isnad1 id=eq.0h3v.s5.675b5e43266e from=translated src=- shape=dd5aecf4 vocab=c8312926
-/
theorem doobFourierCos_generator (ξ ell x : ℝ) :
    doobFourierCosDell ξ ell x = doobFourierCosDxx ξ ell x / 2 +
      Real.tanh x * doobFourierCosDx ξ ell x := by
  dsimp [doobFourierCosDell, doobFourierCosDxx, doobFourierCosDx]
  linear_combination Real.exp (-(ξ ^ 2 * ell) / 2) * ξ * Real.cos (ξ * x) *
    Real.sin (ξ * ell) * tanh_sq_add_sech_sq x

/--
@isnad1 id=eq.0h3v.s5.022a4368f5bc from=translated src=- shape=dd5aecf4 vocab=923b3d0a
-/
theorem doobFourierSin_generator (ξ ell x : ℝ) :
    doobFourierSinDell ξ ell x = doobFourierSinDxx ξ ell x / 2 +
      Real.tanh x * doobFourierSinDx ξ ell x := by
  dsimp [doobFourierSinDell, doobFourierSinDxx, doobFourierSinDx]
  linear_combination Real.exp (-(ξ ^ 2 * ell) / 2) * ξ * Real.sin (ξ * x) *
    Real.sin (ξ * ell) * tanh_sq_add_sech_sq x

/-- The real backward Fourier solution in physical time.-/
def backwardDoobCos (β T ξ t x : ℝ) : ℝ := doobFourierCos ξ (β ^ 2 * (T - t)) x

/-- The imaginary backward Fourier solution in physical time.-/
def backwardDoobSin (β T ξ t x : ℝ) : ℝ := doobFourierSin ξ (β ^ 2 * (T - t)) x

/--
@isnad1 id=eq.0h4v.s4.fe50627a9283 from=translated src=- shape=b5b14209 vocab=42143b88
-/
@[simp] theorem backwardDoobCos_terminal (β T ξ x : ℝ) : backwardDoobCos β T ξ T x = Real.cos (ξ * x) := by
  simp [backwardDoobCos, doobFourierCos]

/--
@isnad1 id=eq.0h4v.s4.7e1be19cfb09 from=translated src=- shape=b5b14209 vocab=0ac220bc
-/
@[simp] theorem backwardDoobSin_terminal (β T ξ x : ℝ) : backwardDoobSin β T ξ T x = Real.sin (ξ * x) := by
  simp [backwardDoobSin, doobFourierSin]

/--
@isnad1 id=contdiff.0h1v.s5.fe9e270a6afb from=translated src=- shape=99645fbc vocab=bfa42e6a
-/
@[fun_prop] theorem doobFourier_contDiff_tanh {n : ℕ∞ω} : ContDiff ℝ n Real.tanh := by
  have he : Real.tanh = (fun x => Real.sinh x / Real.cosh x) := funext Real.tanh_eq_sinh_div_cosh
  rw [he]
  exact Real.contDiff_sinh.div Real.contDiff_cosh (fun x => (Real.cosh_pos x).ne')

/--
@isnad1 id=contdiff.0h1v.s5.b1b7b57b57a4 from=translated src=- shape=99645fbc vocab=6f100824
-/
@[fun_prop] theorem doobFourier_contDiff_sech {n : ℕ∞ω} : ContDiff ℝ n sech := by
  unfold sech
  exact contDiff_const.div Real.contDiff_cosh (fun x => (Real.cosh_pos x).ne')

/-- The Fourier backward solutions are smooth jointly in time and space.
@isnad1 id=contdiff.0h4v.s6.7f1f6bb7b5ca from=translated src=- shape=50ea55ed vocab=54f256ce
-/
theorem contDiff_backwardDoobCos_joint (β T ξ : ℝ) (n : ℕ∞ω) :
    ContDiff ℝ n (fun p : ℝ × ℝ => backwardDoobCos β T ξ p.1 p.2) := by
  unfold backwardDoobCos doobFourierCos
  fun_prop

/--
@isnad1 id=contdiff.0h4v.s6.3f933caa3495 from=translated src=- shape=50ea55ed vocab=f827d4b1
-/
theorem contDiff_backwardDoobSin_joint (β T ξ : ℝ) (n : ℕ∞ω) :
    ContDiff ℝ n (fun p : ℝ × ℝ => backwardDoobSin β T ξ p.1 p.2) := by
  unfold backwardDoobSin doobFourierSin
  fun_prop

/--
@isnad1 id=contdiff.0h5v.s5.4c2357cd7c99 from=translated src=- shape=d8969fc3 vocab=b083d5fc
-/
theorem contDiff_backwardDoobCos_spatial (β T ξ t : ℝ) (n : ℕ∞ω) :
    ContDiff ℝ n (backwardDoobCos β T ξ t) := by
  unfold backwardDoobCos doobFourierCos
  fun_prop

/--
@isnad1 id=contdiff.0h5v.s5.f42dc31f8500 from=translated src=- shape=d8969fc3 vocab=6b482a9b
-/
theorem contDiff_backwardDoobSin_spatial (β T ξ t : ℝ) (n : ℕ∞ω) :
    ContDiff ℝ n (backwardDoobSin β T ξ t) := by
  unfold backwardDoobSin doobFourierSin
  fun_prop

private theorem doobFourier_norm_cos_le (y : ℝ) : ‖Real.cos y‖ ≤ 1 := by
  simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one y

private theorem doobFourier_norm_sin_le (y : ℝ) : ‖Real.sin y‖ ≤ 1 := by
  simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one y

private theorem doobFourier_norm_tanh_le (y : ℝ) : ‖Real.tanh y‖ ≤ 1 := by
  simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one y).le

private theorem doobFourier_factor_bound (ξ ell : ℝ) (hell : 0 ≤ ell) :
    ‖Real.exp (-(ξ ^ 2 * ell) / 2)‖ ≤ 1 := by
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg (sq_nonneg ξ) hell)) (by norm_num)

private theorem norm_prod_le_one {u v : ℝ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) : ‖u * v‖ ≤ 1 := by
  rw [norm_mul]
  simpa only [one_mul] using mul_le_mul hu hv (norm_nonneg _) zero_le_one

/-- A global spatial bound for the Fourier modes on nonnegative remaining variance.
@isnad1 id=le.1h3v.s5.89b821182de5 from=translated src=- shape=a9fb750a vocab=e12df3ed
-/
theorem norm_doobFourierCos_le_two (ξ ell x : ℝ) (hell : 0 ≤ ell) : ‖doobFourierCos ξ ell x‖ ≤ 2 := by
  have h1 := norm_prod_le_one (doobFourier_norm_cos_le (ξ * x)) (doobFourier_norm_cos_le (ξ * ell))
  have h2 := norm_prod_le_one
    (norm_prod_le_one (doobFourier_norm_tanh_le x) (doobFourier_norm_sin_le (ξ * x)))
    (doobFourier_norm_sin_le (ξ * ell))
  unfold doobFourierCos
  rw [norm_mul]
  have hb := (norm_sub_le _ _).trans (add_le_add h1 h2)
  have hmul := mul_le_mul (doobFourier_factor_bound ξ ell hell) hb (norm_nonneg _) zero_le_one
  simpa only [one_mul, show (1 : ℝ) + 1 = 2 by norm_num] using hmul

/--
@isnad1 id=le.1h3v.s5.e1a93a0a87ab from=translated src=- shape=a9fb750a vocab=284a230a
-/
theorem norm_doobFourierSin_le_two (ξ ell x : ℝ) (hell : 0 ≤ ell) : ‖doobFourierSin ξ ell x‖ ≤ 2 := by
  have h1 := norm_prod_le_one (doobFourier_norm_sin_le (ξ * x)) (doobFourier_norm_cos_le (ξ * ell))
  have h2 := norm_prod_le_one
    (norm_prod_le_one (doobFourier_norm_tanh_le x) (doobFourier_norm_cos_le (ξ * x)))
    (doobFourier_norm_sin_le (ξ * ell))
  unfold doobFourierSin
  rw [norm_mul]
  have hb := (norm_add_le _ _).trans (add_le_add h1 h2)
  have hmul := mul_le_mul (doobFourier_factor_bound ξ ell hell) hb (norm_nonneg _) zero_le_one
  simpa only [one_mul, show (1 : ℝ) + 1 = 2 by norm_num] using hmul

/-- The spatial derivatives are bounded uniformly in space and nonnegative variance.
@isnad1 id=le.1h3v.s5.e300cf699ad8 from=translated src=- shape=e1e0499a vocab=619ef528
-/
theorem norm_doobFourierCosDx_le (ξ ell x : ℝ) (hell : 0 ≤ ell) :
    ‖doobFourierCosDx ξ ell x‖ ≤ 1 + 2 * |ξ| := by
  have ht : ‖Real.tanh x‖ ≤ 1 := doobFourier_norm_tanh_le x
  have hs : ‖sech x ^ 2‖ ≤ 1 := by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact sech_sq_le_one x
  have h1 : ‖-ξ * Real.sin (ξ * x) * Real.cos (ξ * ell)‖ ≤ |ξ| := by
    rw [norm_mul, norm_mul, norm_neg, Real.norm_eq_abs ξ]
    calc
      _ ≤ |ξ| * 1 * 1 := by gcongr <;> first | exact doobFourier_norm_sin_le _ | exact doobFourier_norm_cos_le _
      _ = _ := by ring
  have h2 : ‖sech x ^ 2 * Real.sin (ξ * x)‖ ≤ 1 := norm_prod_le_one hs (doobFourier_norm_sin_le _)
  have h3 : ‖ξ * Real.tanh x * Real.cos (ξ * x)‖ ≤ |ξ| := by
    rw [norm_mul, norm_mul, Real.norm_eq_abs ξ]
    calc
      _ ≤ |ξ| * 1 * 1 := by gcongr <;> first | exact ht | exact doobFourier_norm_cos_le _
      _ = _ := by ring
  have h4 : ‖(sech x ^ 2 * Real.sin (ξ * x) + ξ * Real.tanh x * Real.cos (ξ * x)) * Real.sin (ξ * ell)‖ ≤
      1 + |ξ| := by
    rw [norm_mul]
    calc
      _ ≤ (1 + |ξ|) * 1 := mul_le_mul ((norm_add_le _ _).trans (add_le_add h2 h3))
        (doobFourier_norm_sin_le _) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  unfold doobFourierCosDx
  rw [norm_mul]
  have hb := (norm_sub_le _ _).trans (add_le_add h1 h4)
  have hm := mul_le_mul (doobFourier_factor_bound ξ ell hell) hb (norm_nonneg _) zero_le_one
  simp only [one_mul] at hm
  linarith

/--
@isnad1 id=le.1h3v.s5.1a448b027671 from=translated src=- shape=e1e0499a vocab=578a9583
-/
theorem norm_doobFourierSinDx_le (ξ ell x : ℝ) (hell : 0 ≤ ell) :
    ‖doobFourierSinDx ξ ell x‖ ≤ 1 + 2 * |ξ| := by
  have ht : ‖Real.tanh x‖ ≤ 1 := doobFourier_norm_tanh_le x
  have hs : ‖sech x ^ 2‖ ≤ 1 := by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact sech_sq_le_one x
  have h1 : ‖ξ * Real.cos (ξ * x) * Real.cos (ξ * ell)‖ ≤ |ξ| := by
    rw [norm_mul, norm_mul, Real.norm_eq_abs ξ]
    calc
      _ ≤ |ξ| * 1 * 1 := by gcongr <;> exact doobFourier_norm_cos_le _
      _ = _ := by ring
  have h2 : ‖sech x ^ 2 * Real.cos (ξ * x)‖ ≤ 1 := norm_prod_le_one hs (doobFourier_norm_cos_le _)
  have h3 : ‖ξ * Real.tanh x * Real.sin (ξ * x)‖ ≤ |ξ| := by
    rw [norm_mul, norm_mul, Real.norm_eq_abs ξ]
    calc
      _ ≤ |ξ| * 1 * 1 := by gcongr <;> first | exact ht | exact doobFourier_norm_sin_le _
      _ = _ := by ring
  have h4 : ‖(sech x ^ 2 * Real.cos (ξ * x) - ξ * Real.tanh x * Real.sin (ξ * x)) * Real.sin (ξ * ell)‖ ≤
      1 + |ξ| := by
    rw [norm_mul]
    calc
      _ ≤ (1 + |ξ|) * 1 := mul_le_mul ((norm_sub_le _ _).trans (add_le_add h2 h3))
        (doobFourier_norm_sin_le _) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  unfold doobFourierSinDx
  rw [norm_mul]
  have hb := (norm_add_le _ _).trans (add_le_add h1 h4)
  have hm := mul_le_mul (doobFourier_factor_bound ξ ell hell) hb (norm_nonneg _) zero_le_one
  simp only [one_mul] at hm
  linarith

/--
@isnad1 id=le.1h5v.s5.90d841f75763 from=translated src=- shape=7c287d92 vocab=c8ec8a9c
-/
theorem norm_backwardDoobCos_le (β T ξ t x : ℝ) (ht : t ≤ T) : ‖backwardDoobCos β T ξ t x‖ ≤ 2 :=
  norm_doobFourierCos_le_two ξ _ x (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr ht))

/--
@isnad1 id=le.1h5v.s5.1bed29b748ec from=translated src=- shape=7c287d92 vocab=c0fce0f1
-/
theorem norm_backwardDoobSin_le (β T ξ t x : ℝ) (ht : t ≤ T) : ‖backwardDoobSin β T ξ t x‖ ≤ 2 :=
  norm_doobFourierSin_le_two ξ _ x (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr ht))

private theorem int_char (μ ξ : ℝ) (v : ℝ≥0) :
    Integrable (fun y : ℝ => Complex.exp ((ξ : ℂ) * y * Complex.I)) (gaussianReal μ v) := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  filter_upwards [] with y
  simpa only [← Complex.ofReal_mul] using (Complex.norm_exp_ofReal_mul_I (ξ * y)).le

/--
@isnad1 id=eq.0h3v.s6.a146ca6766fe from=translated src=- shape=9ecdbaf2 vocab=1e4ee77c
-/
theorem gaussianIntegral_cos (μ ξ : ℝ) (v : ℝ≥0) :
    (∫ y, Real.cos (ξ * y) ∂gaussianReal μ v) =
      Real.exp (-(v : ℝ) * ξ ^ 2 / 2) * Real.cos (ξ * μ) := by
  have hr := congrArg (RCLike.re : ℂ → ℝ) (charFun_gaussianReal (μ := μ) (v := v) ξ)
  rw [charFun_apply_real, ← integral_re (int_char μ ξ v)] at hr
  simpa [Complex.exp_re, ← Complex.ofReal_pow, neg_div] using hr

/--
@isnad1 id=eq.0h3v.s6.cf2ac5a1b239 from=translated src=- shape=9ecdbaf2 vocab=c6341278
-/
theorem gaussianIntegral_sin (μ ξ : ℝ) (v : ℝ≥0) :
    (∫ y, Real.sin (ξ * y) ∂gaussianReal μ v) =
      Real.exp (-(v : ℝ) * ξ ^ 2 / 2) * Real.sin (ξ * μ) := by
  have hr := congrArg (RCLike.im : ℂ → ℝ) (charFun_gaussianReal (μ := μ) (v := v) ξ)
  rw [charFun_apply_real, ← integral_im (int_char μ ξ v)] at hr
  simpa [Complex.exp_im, ← Complex.ofReal_pow, neg_div] using hr
/--
@isnad1 id=eq.2h3v.s7.c21cf42a9698 from=translated src=- shape=2932abed vocab=ea88aa2f
-/
theorem integral_doobOperator_mixture (v : ℝ≥0) (x : ℝ) (ψ : ℝ → ℝ)
    (hp : Integrable ψ (gaussianReal (x + (v : ℝ)) v))
    (hn : Integrable ψ (gaussianReal (x - (v : ℝ)) v)) :
    doobOperator v ψ x =
      positiveDriftWeight x * (∫ y, ψ y ∂gaussianReal (x + (v : ℝ)) v) +
      negativeDriftWeight x * (∫ y, ψ y ∂gaussianReal (x - (v : ℝ)) v) := by
  rw [← integral_coshStateKernel, coshStateKernel_gaussian_mixture,
    integral_add_measure (hp.smul_measure ENNReal.ofReal_ne_top)
      (hn.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure]
  obtain ⟨hp0, hn0⟩ := driftWeights_nonneg x
  rw [ENNReal.toReal_ofReal hp0, ENNReal.toReal_ofReal hn0, smul_eq_mul, smul_eq_mul]

private theorem integral_gaussian_cos_integrable (μ ξ : ℝ) (v : ℝ≥0) :
    Integrable (fun y => Real.cos (ξ * y)) (gaussianReal μ v) := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  exact Filter.Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (ξ * y))

private theorem integral_gaussian_sin_integrable (μ ξ : ℝ) (v : ℝ≥0) :
    Integrable (fun y => Real.sin (ξ * y)) (gaussianReal μ v) := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  exact Filter.Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (ξ * y))

/--
@isnad1 id=eq.0h1v.s4.9a745dd468b4 from=translated src=- shape=0fc81935 vocab=ff6dfd6d
-/
theorem driftWeights_sub (x : ℝ) : positiveDriftWeight x - negativeDriftWeight x = Real.tanh x := by
  unfold positiveDriftWeight negativeDriftWeight
  rw [← sub_div, Real.tanh_eq_sinh_div_cosh, Real.sinh_eq]
  field_simp

/-- The actual cosh-transform expectation of a real Fourier mode.
@isnad1 id=eq.0h3v.s4.420571bf7efa from=translated src=- shape=8d06f92d vocab=7ce9d14b
-/
theorem doobOperator_cos (v : ℝ≥0) (x ξ : ℝ) :
    doobOperator v (fun y => Real.cos (ξ * y)) x = doobFourierCos ξ (v : ℝ) x := by
  rw [integral_doobOperator_mixture v x _ (integral_gaussian_cos_integrable _ _ _)
    (integral_gaussian_cos_integrable _ _ _), gaussianIntegral_cos, gaussianIntegral_cos]
  unfold doobFourierCos
  rw [mul_add, mul_sub, Real.cos_add, Real.cos_sub]
  have he : -(v : ℝ) * ξ ^ 2 / 2 = -(ξ ^ 2 * (v : ℝ)) / 2 := by ring
  rw [he]
  have hsum := driftWeights_sum x
  have hdiff := driftWeights_sub x
  linear_combination Real.exp (-(ξ ^ 2 * (v : ℝ)) / 2) * Real.cos (ξ * x) * Real.cos (ξ * (v : ℝ)) * hsum -
    Real.exp (-(ξ ^ 2 * (v : ℝ)) / 2) * Real.sin (ξ * x) * Real.sin (ξ * (v : ℝ)) * hdiff

/-- The actual cosh-transform expectation of an imaginary Fourier mode.
@isnad1 id=eq.0h3v.s4.b157d8749ea1 from=translated src=- shape=8d06f92d vocab=eb3207c0
-/
theorem doobOperator_sin (v : ℝ≥0) (x ξ : ℝ) :
    doobOperator v (fun y => Real.sin (ξ * y)) x = doobFourierSin ξ (v : ℝ) x := by
  rw [integral_doobOperator_mixture v x _ (integral_gaussian_sin_integrable _ _ _)
    (integral_gaussian_sin_integrable _ _ _), gaussianIntegral_sin, gaussianIntegral_sin]
  unfold doobFourierSin
  rw [mul_add, mul_sub, Real.sin_add, Real.sin_sub]
  have he : -(v : ℝ) * ξ ^ 2 / 2 = -(ξ ^ 2 * (v : ℝ)) / 2 := by ring
  rw [he]
  have hsum := driftWeights_sum x
  have hdiff := driftWeights_sub x
  linear_combination Real.exp (-(ξ ^ 2 * (v : ℝ)) / 2) * Real.sin (ξ * x) * Real.cos (ξ * (v : ℝ)) * hsum +
    Real.exp (-(ξ ^ 2 * (v : ℝ)) / 2) * Real.cos (ξ * x) * Real.sin (ξ * (v : ℝ)) * hdiff

end Paper
