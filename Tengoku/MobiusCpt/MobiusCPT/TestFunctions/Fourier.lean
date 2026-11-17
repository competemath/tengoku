import Tengoku.Seed.Analysis.Fourier.AddCircle
import Tengoku.Seed.Analysis.Normed.Group.FunctionSeries
import Tengoku.Seed.Analysis.PSeries
import Tengoku.Seed.Analysis.SpecialFunctions.ExpDeriv
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Tengoku.Seed.Order.Filter.AtTopBot.Finset
import Tengoku.MobiusCpt.MobiusCPT.TestFunctions.Complete
import Tengoku.MobiusCpt.MobiusCPT.TestFunctions.Monomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# MobiusCPT.TestFunctions.Fourier

Fourier coefficients, rapid decay, and Fourier convergence in the `C^∞` topology of the
smooth test-function space on the circle.
-/

namespace MobiusCPT

open Filter Function MeasureTheory Set
open AddCircle
open scoped ContDiff Interval Topology

noncomputable section

/-- Positivity of the period used for the additive-circle Fourier model.
@isnad1 id=fact.0h0v.s4.f61dd76c7f3a from=translated src=- shape=d0e17bf9 vocab=fe6d89ed
-/
instance fact_pos_two_mul_pi : Fact ((0 : ℝ) < 2 * Real.pi) :=
  ⟨by positivity⟩

/-- The angle picture of a test function, descended to `ℝ / (2πℤ)`.-/
def toAddCircle (f : TestFn) : AddCircle (2 * Real.pi) → ℂ :=
  (periodic_toAngle f).lift

/-- Evaluation of the descended angle picture at a real representative.
@isnad1 id=eq.0h2v.s5.34c515c23e24 from=translated src=- shape=1cbbed34 vocab=b0548b3e
-/
@[simp] theorem toAddCircle_coe (f : TestFn) (θ : ℝ) :
    toAddCircle f (θ : AddCircle (2 * Real.pi)) = toAngle f θ :=
  Function.Periodic.lift_coe _ _

/-- The descended angle picture is continuous on the additive circle.
@isnad1 id=continuo.0h1v.s6.5c566395d2b9 from=translated src=- shape=ac2fd398 vocab=22687ea3
-/
theorem continuous_toAddCircle (f : TestFn) : Continuous (toAddCircle f) := by
  unfold toAddCircle Function.Periodic.lift
  exact (contDiff_toAngle f).continuous.quotient_liftOn' _

/-- [T26], §3; the `j`-th angle derivative as a continuous function on `ℝ / (2πℤ)`.-/
def angleDerivCircle (j : ℕ) (f : TestFn) : C(AddCircle (2 * Real.pi), ℂ) where
  toFun := (periodic_angleDeriv j f).lift
  continuous_toFun := by
    unfold Function.Periodic.lift
    exact (contDiff_angleDeriv j f).continuous.quotient_liftOn' _

/-- Evaluation of a descended angle derivative at a real representative.
@isnad1 id=eq.0h3v.s7.c96e9b30e1d9 from=translated src=- shape=94484f35 vocab=03852cd3
-/
@[simp] theorem angleDerivCircle_coe (j : ℕ) (f : TestFn) (θ : ℝ) :
    angleDerivCircle j f (θ : AddCircle (2 * Real.pi)) = angleDeriv j f θ :=
  rfl

/-- The zeroth descended angle derivative is the descended angle picture.
@isnad1 id=eq.0h1v.s7.bd26869adf5f from=translated src=- shape=c23ca5ea vocab=37fcb07f
-/
theorem angleDerivCircle_zero (f : TestFn) :
    ⇑(angleDerivCircle 0 f) = toAddCircle f := by
  funext x
  refine Quotient.inductionOn' x ?_
  intro θ
  simp [angleDeriv, iteratedDeriv_zero]

/-- [T26], §3; the real-angle and additive-circle uniform norms agree. See also
`norm_angleDerivB_eq_norm_angleDerivS1` for the literal `Circle`-carrier version of this
statement, i.e. the sup norm over the space's own carrier `Circle` used by `TestFn`.
@isnad1 id=eq.0h2v.s7.78aeed98d977 from=translated src=- shape=3b496a88 vocab=9a728ddc
-/
theorem norm_angleDerivB_eq (j : ℕ) (f : TestFn) :
    ‖angleDerivB j f‖ = ‖angleDerivCircle j f‖ := by
  apply le_antisymm
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).2
    intro θ
    rw [angleDerivB_apply, ← angleDerivCircle_coe]
    exact ContinuousMap.norm_coe_le_norm (angleDerivCircle j f)
      (θ : AddCircle (2 * Real.pi))
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
    intro x
    refine Quotient.inductionOn' x ?_
    intro θ
    rw [angleDerivCircle_coe]
    exact norm_angleDeriv_le j f θ

/-- [T26], §2–§3; the `j`-th angle derivative as a continuous function on the `Circle` carrier
that `TestFn` is built over, transported from `angleDerivCircle` along the standard
homeomorphism `AddCircle (2 * π) ≃ₜ Circle`.-/
def angleDerivS1 (j : ℕ) (f : TestFn) : C(Circle, ℂ) :=
  (angleDerivCircle j f).comp
    (AddCircle.homeomorphCircle'.symm : C(Circle, AddCircle (2 * Real.pi)))

/-- Evaluation of the `Circle`-carrier angle derivative at `Circle.exp θ` agrees with the
real-angle derivative at `θ`.
@isnad1 id=eq.0h3v.s6.df3ed8291c25 from=translated src=- shape=dc3681f0 vocab=42be361b
-/
@[simp] theorem angleDerivS1_apply_exp (j : ℕ) (f : TestFn) (θ : ℝ) :
    angleDerivS1 j f (Circle.exp θ) = angleDeriv j f θ := by
  have hpt : AddCircle.homeomorphCircle'.symm (Circle.exp θ) = (θ : AddCircle (2 * Real.pi)) :=
    AddCircle.homeomorphCircle'.symm_apply_eq.2 (AddCircle.homeomorphCircle'_apply_mk θ).symm
  simp only [angleDerivS1, ContinuousMap.comp_apply, ContinuousMap.coe_coe, hpt,
    angleDerivCircle_coe]

/-- Pre-composition with the homeomorphism `AddCircle (2 * π) ≃ₜ Circle` preserves the uniform
norm: the `Circle`-carrier and additive-circle sup norms agree.
@isnad1 id=eq.0h2v.s7.f643bf06cdcf from=translated src=- shape=40bd061d vocab=63845a01
-/
theorem norm_angleDerivS1_eq_norm_angleDerivCircle (j : ℕ) (f : TestFn) :
    ‖angleDerivS1 j f‖ = ‖angleDerivCircle j f‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
    intro x
    simp only [angleDerivS1, ContinuousMap.comp_apply, ContinuousMap.coe_coe]
    exact ContinuousMap.norm_coe_le_norm (angleDerivCircle j f) _
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
    intro y
    have hx : angleDerivS1 j f (AddCircle.homeomorphCircle' y) = angleDerivCircle j f y := by
      simp only [angleDerivS1, ContinuousMap.comp_apply, ContinuousMap.coe_coe,
        Homeomorph.symm_apply_apply]
    rw [← hx]
    exact ContinuousMap.norm_coe_le_norm (angleDerivS1 j f) _

/-- [T26], §2–§3; the filed item: the bounded real-angle sup norm agrees with the uniform norm
of the `j`-th angle derivative on the literal `Circle` carrier used by `TestFn`.
@isnad1 id=eq.0h2v.s6.0e3908fa7f19 from=translated src=- shape=307f7270 vocab=cf725ae5
-/
theorem norm_angleDerivB_eq_norm_angleDerivS1 (j : ℕ) (f : TestFn) :
    ‖angleDerivB j f‖ = ‖angleDerivS1 j f‖ := by
  rw [norm_angleDerivB_eq, norm_angleDerivS1_eq_norm_angleDerivCircle]

/-- [T26], §3; the `n`-th Fourier coefficient of a smooth test function, defined through
mathlib's normalized-Haar `fourierCoeff` on `AddCircle (2 * Real.pi)`.-/
def fourierCoef (f : TestFn) (n : ℤ) : ℂ :=
  fourierCoeff (toAddCircle f) n

/-- The Fourier coefficient of the `j`-th angle derivative.-/
def fourierCoefDeriv (j : ℕ) (f : TestFn) (n : ℤ) : ℂ :=
  fourierCoeff (angleDerivCircle j f) n

/-- The derivative coefficient at order zero is the original Fourier coefficient.
@isnad1 id=eq.0h2v.s4.c6dc956038bb from=translated src=- shape=20477b1a vocab=a42bda91
-/
theorem fourierCoefDeriv_zero (f : TestFn) (n : ℤ) :
    fourierCoefDeriv 0 f n = fourierCoef f n := by
  rw [fourierCoefDeriv, fourierCoef, angleDerivCircle_zero]

/-- The additive-circle Fourier character is the angle picture of the corresponding monomial.
@isnad1 id=eq.0h2v.s7.9a95668c7ae4 from=translated src=- shape=6c93f148 vocab=a938fd43
-/
theorem fourier_eq_toAngle_monomial (n : ℤ) (θ : ℝ) :
    fourier n (θ : AddCircle (2 * Real.pi)) = toAngle (monomial n) θ := by
  rw [fourier_coe_apply, toAngle_monomial]
  congr 1
  field_simp [Real.pi_ne_zero]
  push_cast
  ring

/-- Descending a monomial to the additive circle gives mathlib's Fourier character.
@isnad1 id=eq.0h1v.s7.0366429c0ddd from=translated src=- shape=1cde72e5 vocab=8b45eca3
-/
theorem toAddCircle_monomial (n : ℤ) :
    toAddCircle (monomial n) = fourier n := by
  funext x
  refine Quotient.inductionOn' x ?_
  intro θ
  rw [toAddCircle_coe, fourier_eq_toAngle_monomial]

/-- The Fourier coefficient of a monomial is the corresponding Kronecker delta.
@isnad1 id=eq.0h2v.s4.0b267580815f from=translated src=- shape=eba2600a vocab=f5b5865f
-/
theorem fourierCoef_monomial (m n : ℤ) :
    fourierCoef (monomial m) n = if n = m then 1 else 0 := by
  rw [fourierCoef, toAddCircle_monomial, fourierCoeff_fourier, Pi.single_apply]

/-- A Fourier coefficient of an angle derivative is bounded by its uniform norm.
@isnad1 id=le.0h3v.s5.b4645e9ee4ed from=translated src=- shape=6042e52b vocab=c4eac6ef
-/
theorem norm_fourierCoefDeriv_le (j : ℕ) (f : TestFn) (n : ℤ) :
    ‖fourierCoefDeriv j f n‖ ≤ ‖angleDerivB j f‖ := by
  unfold fourierCoefDeriv fourierCoeff
  calc
    ‖∫ t : AddCircle (2 * Real.pi), fourier (-n) t • angleDerivCircle j f t
        ∂haarAddCircle‖ ≤
        ‖angleDerivB j f‖ * (@haarAddCircle (2 * Real.pi) _).real univ := by
      apply norm_integral_le_of_norm_le_const
      apply Eventually.of_forall
      intro t
      refine Quotient.inductionOn' t ?_
      intro θ
      rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul, angleDerivCircle_coe]
      exact norm_angleDeriv_le j f θ
    _ = ‖angleDerivB j f‖ := by simp

/-- A Fourier coefficient is bounded by the uniform norm of the original angle function.
@isnad1 id=le.0h2v.s5.e11a5a4e6c2a from=translated src=- shape=94459135 vocab=c2c67486
-/
theorem norm_fourierCoef_le (f : TestFn) (n : ℤ) :
    ‖fourierCoef f n‖ ≤ ‖angleDerivB 0 f‖ := by
  rw [← fourierCoefDeriv_zero f n]
  exact norm_fourierCoefDeriv_le 0 f n

private theorem angleDerivCircle_eq_liftIoc (j : ℕ) (f : TestFn) :
    ⇑(angleDerivCircle j f) =
      AddCircle.liftIoc (2 * Real.pi) 0 (angleDeriv j f) := by
  funext x
  obtain ⟨θ, hθ, rfl⟩ := AddCircle.eq_coe_Ioc x
  rw [angleDerivCircle_coe, AddCircle.liftIoc_coe_apply]
  simpa only [zero_add] using hθ

private theorem fourierCoefDeriv_eq_fourierCoeffOn (j : ℕ) (f : TestFn) (n : ℤ) :
    fourierCoefDeriv j f n =
      fourierCoeffOn (show (0 : ℝ) < 2 * Real.pi by positivity) (angleDeriv j f) n := by
  have h := fourierCoeff_liftIoc_eq (T := 2 * Real.pi) (a := 0) (angleDeriv j f) n
  simp only [zero_add] at h
  rw [fourierCoefDeriv, angleDerivCircle_eq_liftIoc, h]

private theorem hasDerivAt_angleDeriv (j : ℕ) (f : TestFn) (θ : ℝ) :
    HasDerivAt (angleDeriv j f) (angleDeriv (j + 1) f θ) θ := by
  rw [angleDeriv, angleDeriv, iteratedDeriv_succ]
  exact ((contDiff_angleDeriv j f).differentiable (by simp)).differentiableAt.hasDerivAt

/-- [T26], §3; differentiation multiplies the `n`-th Fourier coefficient by `n i`.
This identity includes the zero mode.
@isnad1 id=eq.0h3v.s5.7f25f6fc3c5e from=translated src=- shape=604b9f8c vocab=942dc8e6
-/
theorem fourierCoefDeriv_succ (j : ℕ) (f : TestFn) (n : ℤ) :
    fourierCoefDeriv (j + 1) f n =
      (n : ℂ) * Complex.I * fourierCoefDeriv j f n := by
  by_cases hn : n = 0
  · subst n
    simp only [Int.cast_zero, zero_mul]
    rw [fourierCoefDeriv, fourierCoeff_eq_intervalIntegral _ 0 0]
    simp only [neg_zero, fourier_zero, one_smul, zero_add]
    simp_rw [angleDerivCircle_coe]
    have hderiv : deriv (angleDeriv j f) = angleDeriv (j + 1) f := by
      funext θ
      exact (hasDerivAt_angleDeriv j f θ).deriv
    have hftc :
        ∫ θ in (0 : ℝ)..2 * Real.pi, angleDeriv (j + 1) f θ =
          angleDeriv j f (2 * Real.pi) - angleDeriv j f 0 := by
      apply intervalIntegral.integral_deriv_eq_sub' (angleDeriv j f) hderiv
      · intro θ _
        exact ((contDiff_angleDeriv j f).differentiable (by simp)).differentiableAt
      · exact (contDiff_angleDeriv (j + 1) f).continuous.continuousOn
    rw [hftc]
    have hperiod := periodic_angleDeriv j f 0
    simp only [zero_add] at hperiod
    rw [hperiod, sub_self, smul_zero]
  · have hibp := fourierCoeffOn_of_hasDerivAt
        (show (0 : ℝ) < 2 * Real.pi by positivity) hn
        (fun θ _ => hasDerivAt_angleDeriv j f θ)
        ((contDiff_angleDeriv (j + 1) f).continuous.intervalIntegrable 0 (2 * Real.pi))
    have hperiod := periodic_angleDeriv j f 0
    simp only [zero_add] at hperiod
    simp only [hperiod, sub_self, mul_zero, zero_sub] at hibp
    rw [fourierCoefDeriv_eq_fourierCoeffOn,
      fourierCoefDeriv_eq_fourierCoeffOn, hibp]
    field_simp [hn, Real.pi_ne_zero, Complex.I_ne_zero]
    push_cast
    ring

/-- [T26], §3; the `j`-th derivative coefficient is `(n i)^j` times the original
coefficient.
@isnad1 id=eq.0h3v.s5.dfa4e34a7de3 from=translated src=- shape=eeab47dc vocab=53b5d809
-/
theorem fourierCoefDeriv_eq (j : ℕ) (f : TestFn) (n : ℤ) :
    fourierCoefDeriv j f n =
      ((n : ℂ) * Complex.I) ^ j * fourierCoef f n := by
  induction j with
  | zero =>
      simp only [pow_zero, one_mul]
      exact fourierCoefDeriv_zero f n
  | succ j ih =>
      rw [fourierCoefDeriv_succ, ih, pow_succ]
      ring

/-- [T26], §3; Fourier coefficients decay with every prescribed polynomial weight.
@isnad1 id=le.0h3v.s6.e9546fc420e0 from=translated src=- shape=d0ae7e9c vocab=e501afc6
-/
theorem norm_fourierCoef_mul_pow_le (j : ℕ) (f : TestFn) (n : ℤ) :
    |(n : ℝ)| ^ j * ‖fourierCoef f n‖ ≤ ‖angleDerivB j f‖ := by
  have h := norm_fourierCoefDeriv_le j f n
  rw [fourierCoefDeriv_eq, norm_mul, norm_pow, norm_mul,
    Complex.norm_intCast, Complex.norm_I, mul_one] at h
  exact h

/-- [T26], §3; rapid decay bounded by the literal `C^j` seminorm.
@isnad1 id=le.0h3v.s5.3019508bc234 from=translated src=- shape=f5c30547 vocab=4870248e
-/
theorem norm_fourierCoef_mul_pow_le_cnorm (j : ℕ) (f : TestFn) (n : ℤ) :
    |(n : ℝ)| ^ j * ‖fourierCoef f n‖ ≤ (cnorm j f : ℝ) := by
  refine (norm_fourierCoef_mul_pow_le j f n).trans ?_
  rw [cnorm_eq]
  exact Finset.single_le_sum (fun k _ => norm_nonneg (angleDerivB k f)) (by simp)

/-- [T26], §3; every polynomially weighted sequence of Fourier coefficients is summable.
@isnad1 id=summable.0h2v.s5.4dea316b8790 from=translated src=- shape=52ac3386 vocab=3df170d7
-/
theorem summable_norm_fourierCoef_mul_pow (j : ℕ) (f : TestFn) :
    Summable (fun n : ℤ => |(n : ℝ)| ^ j * ‖fourierCoef f n‖) := by
  let C : ℝ := ‖angleDerivB (j + 2) f‖
  have hmajor : Summable (fun n : ℤ => C * (1 / (n : ℝ) ^ 2)) :=
    (Real.summable_one_div_int_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left C
  apply hmajor.of_norm_bounded_eventually
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with n hn
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have habs : |(n : ℝ)| ≠ 0 := abs_ne_zero.mpr hnreal
  have hdecay := norm_fourierCoef_mul_pow_le (j + 2) f n
  have hnonneg : 0 ≤ |(n : ℝ)| ^ j * ‖fourierCoef f n‖ :=
    mul_nonneg (pow_nonneg (abs_nonneg _) _) (norm_nonneg _)
  rw [Real.norm_of_nonneg hnonneg]
  calc
    |(n : ℝ)| ^ j * ‖fourierCoef f n‖ =
        (|(n : ℝ)| ^ (j + 2) * ‖fourierCoef f n‖) / |(n : ℝ)| ^ 2 := by
          field_simp [habs]
          ring
    _ ≤ C / |(n : ℝ)| ^ 2 :=
      div_le_div_of_nonneg_right hdecay (sq_nonneg _)
    _ = C * (1 / (n : ℝ) ^ 2) := by rw [sq_abs]; ring

private theorem hasDerivAt_toAngle_monomial (n : ℤ) (θ : ℝ) :
    HasDerivAt (toAngle (monomial n))
      (((n : ℂ) * Complex.I) * toAngle (monomial n) θ) θ := by
  have h := hasDerivAt_fourier (2 * Real.pi) n θ
  convert h using 1
  · funext x
    exact (fourier_eq_toAngle_monomial n x).symm
  · rw [fourier_eq_toAngle_monomial]
    field_simp [Real.pi_ne_zero]
    push_cast
    ring

/-- The `j`-th angle derivative of a monomial is `(n i)^j exp(n θ i)`.
@isnad1 id=eq.0h3v.s6.835312cef684 from=translated src=- shape=2413f763 vocab=38b4fd06
-/
theorem angleDeriv_monomial (j : ℕ) (n : ℤ) (θ : ℝ) :
    angleDeriv j (monomial n) θ =
      ((n : ℂ) * Complex.I) ^ j *
        Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I) := by
  induction j generalizing θ with
  | zero => simp [angleDeriv, iteratedDeriv_zero, toAngle_monomial]
  | succ j ih =>
      rw [angleDeriv, iteratedDeriv_succ]
      have hfun :
          iteratedDeriv j (toAngle (monomial n)) =
            fun x => ((n : ℂ) * Complex.I) ^ j * toAngle (monomial n) x := by
        funext x
        simpa only [angleDeriv, toAngle_monomial] using ih x
      rw [hfun]
      have h := (hasDerivAt_toAngle_monomial n θ).const_mul
        (((n : ℂ) * Complex.I) ^ j)
      rw [h.deriv, toAngle_monomial, pow_succ]
      ring

/-- Every angle derivative is the pointwise sum of its differentiated Fourier series.
@isnad1 id=hassum.0h3v.s6.10eae8d747e6 from=translated src=- shape=7c1f52c7 vocab=6bf93a4b
-/
theorem hasSum_angleDeriv (j : ℕ) (f : TestFn) (θ : ℝ) :
    HasSum
      (fun n : ℤ => fourierCoef f n * ((n : ℂ) * Complex.I) ^ j *
        Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I))
      (angleDeriv j f θ) := by
  have hs : Summable (fun n : ℤ => ((n : ℂ) * Complex.I) ^ j * fourierCoef f n) := by
    apply (summable_norm_fourierCoef_mul_pow j f).of_norm_bounded
    intro n
    rw [norm_mul, norm_pow, norm_mul, Complex.norm_intCast, Complex.norm_I, mul_one]
  have hcoeff :
      fourierCoeff (angleDerivCircle j f) =
        fun n : ℤ => ((n : ℂ) * Complex.I) ^ j * fourierCoef f n := by
    funext n
    exact fourierCoefDeriv_eq j f n
  have hs' : Summable (fourierCoeff (angleDerivCircle j f)) := by
    rw [hcoeff]
    exact hs
  have h := has_pointwise_sum_fourier_series_of_summable
    (f := angleDerivCircle j f) hs' (θ : AddCircle (2 * Real.pi))
  have h' :
      HasSum
        (fun n : ℤ => fourierCoef f n * ((n : ℂ) * Complex.I) ^ j *
          fourier n (θ : AddCircle (2 * Real.pi)))
        (angleDerivCircle j f (θ : AddCircle (2 * Real.pi))) := by
    apply h.congr_fun
    intro n
    rw [hcoeff]
    simp only [smul_eq_mul]
    ring
  simpa only [angleDerivCircle_coe, fourier_eq_toAngle_monomial, toAngle_monomial] using h'

private theorem norm_angleDerivB_smul_monomial_le
    (j : ℕ) (c : ℂ) (n : ℤ) :
    ‖angleDerivB j (c • monomial n)‖ ≤ |(n : ℝ)| ^ j * ‖c‖ := by
  rw [BoundedContinuousFunction.norm_le (mul_nonneg (pow_nonneg (abs_nonneg _) _)
    (norm_nonneg _))]
  intro θ
  rw [angleDerivB_apply]
  have hsmul := congrFun (angleDeriv_smul j c (monomial n)) θ
  rw [hsmul, Pi.smul_apply, smul_eq_mul, angleDeriv_monomial]
  rw [norm_mul, norm_mul, norm_pow, norm_mul, Complex.norm_intCast, Complex.norm_I,
    mul_one]
  have hexp :
      ‖Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I)‖ = 1 := by
    convert Complex.norm_exp_ofReal_mul_I ((n : ℝ) * θ) using 1
    congr 1
    push_cast
    ring
  rw [hexp, mul_one]
  exact le_of_eq (by ring)

private theorem hasSum_angleDerivB (j : ℕ) (f : TestFn) :
    HasSum (fun n : ℤ => angleDerivB j (fourierCoef f n • monomial n))
      (angleDerivB j f) := by
  have hs : Summable (fun n : ℤ => angleDerivB j (fourierCoef f n • monomial n)) := by
    apply (summable_norm_fourierCoef_mul_pow j f).of_norm_bounded
    intro n
    exact norm_angleDerivB_smul_monomial_le j (fourierCoef f n) n
  have htarget :
      ∑' n : ℤ, angleDerivB j (fourierCoef f n • monomial n) = angleDerivB j f := by
    apply BoundedContinuousFunction.ext
    intro θ
    have heval := (BoundedContinuousFunction.evalCLM ℂ θ).hasSum hs.hasSum
    have hpoint := hasSum_angleDeriv j f θ
    apply HasSum.unique heval
    convert hpoint using 1
    · funext n
      simp only [BoundedContinuousFunction.evalCLM_apply]
      rw [angleDerivB_apply]
      have hsmul := congrFun (angleDeriv_smul j (fourierCoef f n) (monomial n)) θ
      rw [hsmul, Pi.smul_apply, smul_eq_mul, angleDeriv_monomial]
      ring
    · exact angleDerivB_apply j f θ
  rw [← htarget]
  exact hs.hasSum

/-- [T26], §3; the symmetric Fourier sum through frequency `N`.-/
def fourierPartialSum (f : TestFn) (N : ℕ) : TestFn :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoef f n • monomial n

/-- [T26], §3; the Fourier series of a test function sums to it in the `C^∞(S¹)` topology.
@isnad1 id=hassum.0h1v.s4.16b51cf7708c from=translated src=- shape=42d46cf3 vocab=08ccce88
-/
theorem hasSum_fourierSeries (f : TestFn) :
    HasSum (fun n : ℤ => fourierCoef f n • monomial n) f := by
  refine (isInducing_angleDerivs.tendsto_nhds_iff).mpr ?_
  rw [tendsto_pi_nhds]
  intro j
  have hswap : ∀ i : Finset ℤ,
      angleDerivB j (∑ x ∈ i, fourierCoef f x • monomial x)
        = ∑ x ∈ i, angleDerivB j (fourierCoef f x • monomial x) := by
    intro i
    exact map_sum (angleDerivBₗ j) _ i
  simp only [Function.comp_apply, angleDerivsₗ, LinearMap.coe_mk, AddHom.coe_mk,
    hswap]
  exact hasSum_angleDerivB j f

/-- [T26], §3; symmetric Fourier partial sums converge in the `C^∞(S¹)` topology.
@isnad1 id=tendsto.0h1v.s3.76bb52b82cec from=translated src=- shape=4ed846c1 vocab=7c070ae6
-/
theorem tendsto_fourierPartialSum (f : TestFn) :
    Tendsto (fourierPartialSum f) atTop (𝓝 f) := by
  have hfinset :
      Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) atTop atTop := by
    refine tendsto_atTop_finset_of_monotone (β := ℕ) ?_ ?_
    · intro M N hMN
      exact Finset.Icc_subset_Icc (neg_le_neg (Int.ofNat_le.2 hMN))
        (Int.ofNat_le.2 hMN)
    · intro n
      refine ⟨n.natAbs, ?_⟩
      rw [Finset.mem_Icc]
      constructor
      · simpa only [Int.natCast_natAbs] using neg_abs_le n
      · simpa only [Int.natCast_natAbs] using le_abs_self n
  exact (hasSum_fourierSeries f).comp hfinset

/-- Convergence of symmetric Fourier partial sums in every literal `C^N` seminorm.
@isnad1 id=tendsto.0h2v.s5.16cc308ce24f from=translated src=- shape=43f4b5b4 vocab=1c9cdf69
-/
theorem tendsto_cnorm_fourierPartialSum (N : ℕ) (f : TestFn) :
    Tendsto
      (fun M => ((cnorm N (fourierPartialSum f M - f) : NNReal) : ℝ))
      atTop (𝓝 0) :=
  (tendsto_iff_cnorm (fourierPartialSum f) f).mp
    (tendsto_fourierPartialSum f) N

end

end MobiusCPT
