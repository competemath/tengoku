import Tengoku.Seed.Probability.Distributions.Gaussian.Real
import Tengoku.Seed.Probability.HasLaw
import Tengoku.Seed.Probability.Moments.SubGaussian
import Tengoku.Seed.Probability.Independence.Basic
import Tengoku.Seed.MeasureTheory.Integral.Gamma

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The standard Gaussian law and the standard Gaussian vector

A standard Gaussian scalar is `HasLaw g (gaussianReal 0 1) μ`; a standard Gaussian vector is
`HasLaw x (gaussianVector n) μ`, where `gaussianVector n` is the product measure
`Measure.pi fun _ : n => gaussianReal 0 1` on `n → ℝ`.

* `gaussianVector`, `hasLaw_eval_gaussianVector`, `iIndepFun_eval_gaussianVector`,
  `hasLaw_gaussianVector_of_iIndepFun`, `HasLaw.hasLaw_eval_gaussianReal`,
  `HasLaw.iIndepFun_eval_of_gaussianVector`: the product law and its coordinates;
* `integrable_pow_gaussianReal`, `integral_pow_three_gaussianReal`,
  `integral_pow_four_gaussianReal`: moments of `N(0, 1)`;
* `memLp_two_of_hasLaw_gaussianReal`, `integral_eq_zero_of_hasLaw_gaussianReal`,
  `integral_sq_eq_one_of_hasLaw_gaussianReal`, `integrable_pow_four_of_hasLaw_gaussianReal`,
  `integral_pow_four_eq_three_of_hasLaw_gaussianReal`, `integrable_exp_mul_of_hasLaw_gaussianReal`:
  moments of a standard Gaussian variable;
* `hasSubgaussianMGF_id_gaussianReal`, `hasSubgaussianMGF_of_hasLaw_gaussianReal`: `N(0, v)` is
  sub-Gaussian with variance proxy `v` (exact mgf bound).

Atlas: `scalar-laws-def`, `gaussian-matrix-def`, `hutchinson-variance`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace NLAlib

/-- The standard Gaussian vector law on `n → ℝ`: the product of `n` independent copies of
`gaussianReal 0 1`. An `abbrev`, so that Mathlib's `Measure.pi` API applies directly; the
bridges to `stdGaussian (EuclideanSpace ℝ n)` are `gaussianVector_map_toLp_eq_stdGaussian`
(`Probability/Gaussian/Basic/StandardVector`) and to `gaussianMatrix m n`
(`RandomMatrix/Gaussian/Basic/GaussianMatrix`). Vershynin 2018, §3.3.
atlas: scalar-laws-def-/
abbrev gaussianVector (n : Type*) [Fintype n] : Measure (n → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

/-- Each coordinate of the standard Gaussian vector is a standard Gaussian.
@isnad1 id=haslaw.0h2v.s5.43bc03971d7f from=translated src=- shape=d8b18e81 vocab=bbef1014
-/
theorem hasLaw_eval_gaussianVector {n : Type*} [Fintype n] (i : n) :
    HasLaw (fun x : n → ℝ => x i) (gaussianReal 0 1) (gaussianVector n) :=
  (measurePreserving_eval (fun _ : n => gaussianReal 0 1) i).hasLaw

/-- The coordinates of the standard Gaussian vector are independent.
@isnad1 id=iindepfu.0h1v.s5.67643b654957 from=translated src=- shape=253b2850 vocab=0254b4cf
-/
theorem iIndepFun_eval_gaussianVector (n : Type*) [Fintype n] :
    iIndepFun (fun (i : n) (x : n → ℝ) => x i) (gaussianVector n) :=
  iIndepFun_pi (fun _ => aemeasurable_id)

/-- Independent standard Gaussian coordinates form a standard Gaussian vector.
@isnad1 id=haslaw.2h4v.s6.008451edb738 from=translated src=- shape=cf283b7e vocab=0aad3664
-/
theorem hasLaw_gaussianVector_of_iIndepFun {Ω n : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [Fintype n] {x : n → Ω → ℝ} (hx : ∀ i, HasLaw (x i) (gaussianReal 0 1) μ)
    (hind : iIndepFun x μ) :
    HasLaw (fun ω i => x i ω) (gaussianVector n) μ :=
  hind.hasLaw_pi hx

/-- A coordinate of a standard Gaussian vector is a standard Gaussian.
@isnad1 id=haslaw.1h5v.s6.17006487ee94 from=translated src=- shape=8ff9dff1 vocab=9ce5783a
-/
theorem _root_.ProbabilityTheory.HasLaw.hasLaw_eval_gaussianReal {Ω n : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [Fintype n] {x : Ω → n → ℝ}
    (hx : HasLaw x (gaussianVector n) μ) (i : n) :
    HasLaw (fun ω => x ω i) (gaussianReal 0 1) μ :=
  (hasLaw_eval_gaussianVector i).comp hx

/-- The coordinates of a standard Gaussian vector are independent.
@isnad1 id=iindepfu.1h4v.s5.1c931a26e6ff from=translated src=- shape=ef0d444f vocab=d49deec9
-/
theorem _root_.ProbabilityTheory.HasLaw.iIndepFun_eval_of_gaussianVector {Ω n : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [Fintype n] {x : Ω → n → ℝ}
    (hx : HasLaw x (gaussianVector n) μ) :
    iIndepFun (fun i ω => x ω i) μ := by
  have := hx.isProbabilityMeasure
  exact (iIndepFun_iff_hasLaw_pi_pi (fun i => hx.hasLaw_eval_gaussianReal i)).2 hx

/-- Every monomial `x ↦ x^k` is integrable for the standard Gaussian.
@isnad1 id=integrab.0h1v.s5.3745ac37a0b0 from=translated src=- shape=65b702a7 vocab=49f0f850
-/
theorem integrable_pow_gaussianReal (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 1) := by
  have h := (memLp_id_gaussianReal (μ := 0) (v := 1) (k : NNReal)).integrable_norm_pow'
  refine h.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  simp [norm_pow]

/-- The third moment of a standard Gaussian vanishes: `E X³ = 0` (symmetry).
@isnad1 id=eq.0h0v.s5.d17d800cba24 from=translated src=- shape=ed0f2aee vocab=4960fe00
-/
theorem integral_pow_three_gaussianReal : ∫ x, x ^ 3 ∂(gaussianReal 0 1) = 0 := by
  have h : ∫ x, x ^ 3 ∂(gaussianReal 0 1) = ∫ x, (-x) ^ 3 ∂(gaussianReal 0 1) := by
    conv_lhs => rw [← neg_zero, ← gaussianReal_map_neg (μ := 0) (v := 1)]
    rw [integral_map (by fun_prop) (by fun_prop)]
  have h2 : ∫ x, (-x) ^ 3 ∂(gaussianReal 0 1) = - ∫ x, x ^ 3 ∂(gaussianReal 0 1) := by
    rw [← integral_neg]; congr 1; ext x; ring
  linarith

/-- The fourth moment of a standard Gaussian: `E X⁴ = 3`.
@isnad1 id=eq.0h0v.s5.0928981e36b3 from=translated src=- shape=ed0f2aee vocab=4960fe00
-/
theorem integral_pow_four_gaussianReal : ∫ x, x ^ 4 ∂(gaussianReal 0 1) = 3 := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  have h1 : ∀ x : ℝ, gaussianPDFReal 0 1 x • x ^ 4
      = (fun y : ℝ => (√(2 * Real.pi))⁻¹ * (y ^ (4:ℝ) * Real.exp (-(1/2) * y ^ (2:ℝ)))) |x| := by
    intro x
    simp only [gaussianPDFReal, smul_eq_mul, NNReal.coe_one, mul_one, sub_zero]
    have e4 : |x| ^ (4:ℝ) = x ^ 4 := by
      rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast, pow_abs]
      exact abs_of_nonneg (by positivity)
    have e2 : |x| ^ (2:ℝ) = x ^ 2 := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    rw [e4, e2]; ring_nf
  rw [integral_congr_ae (Filter.Eventually.of_forall h1),
    integral_comp_abs (f := fun y : ℝ =>
      (√(2 * Real.pi))⁻¹ * (y ^ (4:ℝ) * Real.exp (-(1/2) * y ^ (2:ℝ)))),
    integral_const_mul,
    integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) (by norm_num)]
  have hg : Real.Gamma ((4 + 1) / 2) = 3 / 4 * √Real.pi := by
    have := Real.Gamma_nat_add_one_add_half 1
    norm_num [Nat.doubleFactorial] at this
    rw [show ((4:ℝ) + 1) / 2 = 5 / 2 by norm_num, this]; ring
  rw [hg]
  have hb : (1/2 : ℝ) ^ (-(4 + 1) / 2 : ℝ) = 4 * √2 := by
    rw [show (-(4 + 1) / 2 : ℝ) = -(2 + 1/2) by norm_num, Real.rpow_neg (by norm_num),
      Real.rpow_add (by norm_num), Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow,
      Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow, ← Real.sqrt_eq_rpow]
    norm_num
    field_simp
  rw [hb, Real.sqrt_mul (by norm_num)]
  have : (0:ℝ) < √2 := by positivity
  have : (0:ℝ) < √Real.pi := by positivity
  field_simp

section HasLawGaussianReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {g : Ω → ℝ}

/-- A standard Gaussian variable is square integrable. Avron–Toledo 2011, Lemma 5.
@isnad1 id=memlp.1h3v.s6.af1ef979bda0 from=translated src=- shape=7e005d80 vocab=639b0e04
-/
theorem memLp_two_of_hasLaw_gaussianReal (hlaw : HasLaw g (gaussianReal 0 1) μ) :
    MemLp g 2 μ := by
  have h := memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp)
  rw [← hlaw.map_eq] at h
  exact (memLp_map_measure_iff aestronglyMeasurable_id hlaw.aemeasurable).1 h

/-- A standard Gaussian variable has mean zero.
@isnad1 id=eq.1h3v.s5.69d0d21a81e7 from=translated src=- shape=65f5c89c vocab=e97d491e
-/
theorem integral_eq_zero_of_hasLaw_gaussianReal (hlaw : HasLaw g (gaussianReal 0 1) μ) :
    ∫ ω, g ω ∂μ = 0 := by
  have h := integral_id_gaussianReal (μ := 0) (v := 1)
  rw [← hlaw.map_eq, integral_map hlaw.aemeasurable (f := fun x : ℝ => x) (by fun_prop)] at h
  simpa using h

/-- A standard Gaussian variable has second moment one. Avron–Toledo 2011, Lemma 5.
@isnad1 id=eq.1h3v.s6.cdbe2aa96efe from=translated src=- shape=4c3b0cba vocab=32e8533f
-/
theorem integral_sq_eq_one_of_hasLaw_gaussianReal (hlaw : HasLaw g (gaussianReal 0 1) μ) :
    ∫ ω, g ω ^ 2 ∂μ = 1 := by
  have h := variance_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id.aemeasurable] at h
  simp only [id, integral_id_gaussianReal, sub_zero] at h
  rw [← hlaw.map_eq, integral_map hlaw.aemeasurable (by fun_prop)] at h
  simpa using h

/-- The fourth power of a standard Gaussian variable is integrable.
@isnad1 id=integrab.1h3v.s6.13746f184e1e from=translated src=- shape=4b0be0e3 vocab=42e80020
-/
theorem integrable_pow_four_of_hasLaw_gaussianReal (hlaw : HasLaw g (gaussianReal 0 1) μ) :
    Integrable (fun ω => g ω ^ 4) μ := by
  have h := integrable_pow_gaussianReal 4
  rw [← hlaw.map_eq] at h
  exact (integrable_map_measure (by fun_prop) hlaw.aemeasurable).1 h

/-- A standard Gaussian variable has fourth moment three. Avron–Toledo 2011, Lemma 5.
@isnad1 id=eq.1h3v.s6.1b90e3aa2fbc from=translated src=- shape=4c3b0cba vocab=32e8533f
-/
theorem integral_pow_four_eq_three_of_hasLaw_gaussianReal
    (hlaw : HasLaw g (gaussianReal 0 1) μ) :
    ∫ ω, g ω ^ 4 ∂μ = 3 := by
  have h := integral_pow_four_gaussianReal
  rw [← hlaw.map_eq, integral_map hlaw.aemeasurable (by fun_prop)] at h
  exact h

/-- A standard Gaussian variable has all exponential moments.
@isnad1 id=integrab.1h4v.s6.1e673d22f8b7 from=translated src=- shape=3c26bf24 vocab=b12d0336
-/
theorem integrable_exp_mul_of_hasLaw_gaussianReal (hlaw : HasLaw g (gaussianReal 0 1) μ)
    (c : ℝ) : Integrable (fun ω => Real.exp (c * g ω)) μ := by
  have h := integrable_exp_mul_gaussianReal (μ := 0) (v := 1) c
  rw [← hlaw.map_eq] at h
  exact (integrable_map_measure (by fun_prop) hlaw.aemeasurable).1 h

end HasLawGaussianReal

/-- **A centred Gaussian is sub-Gaussian with its variance as proxy**:
`E[exp(t Y)] = exp(v t²/2)` for `Y ∼ N(0, v)`, so `HasSubgaussianMGF id v (gaussianReal 0 v)`
(with equality in the mgf bound). Vershynin 2018, Example 2.5.8(i); from Mathlib
`mgf_id_gaussianReal`.
atlas: gaussian-matrix-def
@isnad1 id=hassubga.0h1v.s4.a3a2947d13fd from=translated src=- shape=39d76ae6 vocab=1cc04934
-/
theorem hasSubgaussianMGF_id_gaussianReal (v : NNReal) :
    HasSubgaussianMGF id v (gaussianReal 0 v) where
  integrable_exp_mul t := by
    simpa only [id_eq] using integrable_exp_mul_gaussianReal (μ := 0) (v := v) t
  mgf_le t := by
    rw [mgf_id_gaussianReal]
    simp only [zero_mul, zero_add, le_refl]

/-- A standard Gaussian variable is sub-Gaussian with variance proxy `1`.
Vershynin 2018, Example 2.5.8(i).
@isnad1 id=hassubga.1h3v.s5.b279fc25d1db from=translated src=- shape=79f9e4aa vocab=f0fa8625
-/
theorem hasSubgaussianMGF_of_hasLaw_gaussianReal {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {g : Ω → ℝ} (hg : HasLaw g (gaussianReal 0 1) μ) :
    HasSubgaussianMGF g 1 μ := by
  rw [← HasSubgaussianMGF.id_map_iff hg.aemeasurable, hg.map_eq]
  exact hasSubgaussianMGF_id_gaussianReal 1

end NLAlib
