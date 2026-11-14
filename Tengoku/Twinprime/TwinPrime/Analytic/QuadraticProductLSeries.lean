import Tengoku.Twinprime.TwinPrime.Analytic.ZetaContinuation
import Tengoku.Twinprime.TwinPrime.Analytic.QuadraticProductCoefficients

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A four-factor L-series and its regularized value at one

Absolute convergence justifies the convolution identity only on `Re(s)>1`.
The entire regularization requires all three character factors to be
nonprincipal. Distinct nonprincipal quadratic characters satisfy that
condition. No quantitative lower bound for its value at one is asserted.
-/

noncomputable section

open Filter
open scoped Topology

namespace TwinPrime.Analytic

private theorem LSeriesSummable_characterArithmetic {q : ℕ}
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (toArithmeticFunction (χ ·)) s := by
  exact (LSeriesSummable_congr s fun hn =>
    (χ.apply_eq_toArithmeticFunction_apply hn).symm).mpr
      (χ.LSeriesSummable_of_one_lt_re hs)

private theorem LSeries_characterArithmetic {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeries (toArithmeticFunction (χ ·)) s = DirichletCharacter.LFunction χ s := by
  rw [χ.LFunction_eq_LSeries hs]
  exact LSeries_congr (fun hn => (χ.apply_eq_toArithmeticFunction_apply hn).symm) s

/-- A finite convolution becomes the actual product in the half-plane of
absolute convergence. No quadratic or nonprincipal assumptions are needed.
@isnad1 id=eq.1h5v.s8.4f632931c73e from=translated src=- shape=a14b90c8 vocab=2c4a3c28
-/
theorem LSeries_zeta_three_character_convolution {q : ℕ} [NeZero q]
    (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeries (((ArithmeticFunction.zeta : ArithmeticFunction ℂ) *
      toArithmeticFunction (χ₁ ·) * toArithmeticFunction (χ₂ ·) *
        toArithmeticFunction (χ₃ ·)) : ArithmeticFunction ℂ) s =
      riemannZeta s * DirichletCharacter.LFunction χ₁ s *
        DirichletCharacter.LFunction χ₂ s * DirichletCharacter.LFunction χ₃ s := by
  have hz : LSeriesSummable (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s :=
    ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  have h₁ := LSeriesSummable_characterArithmetic χ₁ hs
  have h₂ := LSeriesSummable_characterArithmetic χ₂ hs
  have h₃ := LSeriesSummable_characterArithmetic χ₃ hs
  rw [ArithmeticFunction.LSeries_mul'
      (ArithmeticFunction.LSeriesSummable_mul
        (ArithmeticFunction.LSeriesSummable_mul hz h₁) h₂) h₃,
    ArithmeticFunction.LSeries_mul' (ArithmeticFunction.LSeriesSummable_mul hz h₁) h₂,
    ArithmeticFunction.LSeries_mul' hz h₁]
  simp_rw [ArithmeticFunction.natCoe_apply]
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs,
    LSeries_characterArithmetic χ₁ hs, LSeries_characterArithmetic χ₂ hs,
    LSeries_characterArithmetic χ₃ hs]

/--
@isnad1 id=lseriess.1h4v.s5.3b88ac69d861 from=translated src=- shape=3ef11502 vocab=720bf816
-/
theorem LSeriesSummable_quadraticProductCoefficients {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (quadraticProductCoefficients χ₁ χ₂) s := by
  unfold quadraticProductCoefficients
  exact ArithmeticFunction.LSeriesSummable_mul
    (ArithmeticFunction.LSeriesSummable_mul
      (ArithmeticFunction.LSeriesSummable_mul
        (ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs)
        (LSeriesSummable_characterArithmetic χ₁ hs))
      (LSeriesSummable_characterArithmetic χ₂ hs))
    (LSeriesSummable_characterArithmetic (χ₁ * χ₂) hs)

/-- The positive-coefficient construction represents the actual four-factor
product on the half-plane of absolute convergence.
@isnad1 id=eq.1h4v.s7.1df1d3b5d3f4 from=translated src=- shape=194b6c0a vocab=8847cbe7
-/
theorem LSeries_quadraticProductCoefficients {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeries (quadraticProductCoefficients χ₁ χ₂) s =
      riemannZeta s * DirichletCharacter.LFunction χ₁ s *
        DirichletCharacter.LFunction χ₂ s * DirichletCharacter.LFunction (χ₁ * χ₂) s := by
  simpa only [quadraticProductCoefficients] using
    LSeries_zeta_three_character_convolution χ₁ χ₂ (χ₁ * χ₂) hs

def quadraticLFunctionProduct {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  riemannZeta s * DirichletCharacter.LFunction χ₁ s *
    DirichletCharacter.LFunction χ₂ s * DirichletCharacter.LFunction (χ₁ * χ₂) s

def regularizedQuadraticLFunctionProduct {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  regularizedRiemannZeta s * DirichletCharacter.LFunction χ₁ s *
    DirichletCharacter.LFunction χ₂ s * DirichletCharacter.LFunction (χ₁ * χ₂) s

/-- The algebra only needs the first character to have square one.
@isnad1 id=ne.2h3v.s8.db810ebd6682 from=translated src=- shape=60f62fd6 vocab=b10dfe66
-/
theorem quadratic_character_mul_ne_one_of_ne {q : ℕ}
    (χ₁ χ₂ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1) (hne : χ₁ ≠ χ₂) :
    χ₁ * χ₂ ≠ 1 := by
  intro hmul
  have hinv : χ₁⁻¹ = χ₁ := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hχ₁)
  exact hne (hinv.symm.trans (mul_eq_one_iff_inv_eq.mp hmul))

/--
@isnad1 id=differen.3h3v.s8.0139d22e7aa5 from=translated src=- shape=cfb61c62 vocab=28e8f1c5
-/
theorem differentiable_regularizedQuadraticLFunctionProduct {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1)
    (hχ₁₂ : χ₁ * χ₂ ≠ 1) :
    Differentiable ℂ (regularizedQuadraticLFunctionProduct χ₁ χ₂) := by
  exact ((differentiable_regularizedRiemannZeta.mul
    (DirichletCharacter.differentiable_LFunction hχ₁)).mul
    (DirichletCharacter.differentiable_LFunction hχ₂)).mul
    (DirichletCharacter.differentiable_LFunction hχ₁₂)

/--
@isnad1 id=differen.4h3v.s8.222469fff555 from=translated src=- shape=c329ed8e vocab=2d95741e
-/
theorem differentiable_regularizedQuadraticLFunctionProduct_of_quadratic {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1)
    (hsq : χ₁ ^ 2 = 1) (hne : χ₁ ≠ χ₂) :
    Differentiable ℂ (regularizedQuadraticLFunctionProduct χ₁ χ₂) :=
  differentiable_regularizedQuadraticLFunctionProduct χ₁ χ₂ hχ₁ hχ₂
    (quadratic_character_mul_ne_one_of_ne χ₁ χ₂ hsq hne)

/--
@isnad1 id=eq.0h3v.s7.63e2bf82e0c0 from=translated src=- shape=8386b7e6 vocab=4532a1db
-/
@[simp] theorem regularizedQuadraticLFunctionProduct_one {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) :
    regularizedQuadraticLFunctionProduct χ₁ χ₂ 1 =
      DirichletCharacter.LFunction χ₁ 1 * DirichletCharacter.LFunction χ₂ 1 *
        DirichletCharacter.LFunction (χ₁ * χ₂) 1 := by
  simp [regularizedQuadraticLFunctionProduct]

/--
@isnad1 id=eq.1h4v.s6.71b8d50f023e from=translated src=- shape=76a98136 vocab=8c76d87e
-/
theorem regularizedQuadraticLFunctionProduct_eq {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) (s : ℂ) (hs : s ≠ 1) :
    regularizedQuadraticLFunctionProduct χ₁ χ₂ s =
      (s - 1) * quadraticLFunctionProduct χ₁ χ₂ s := by
  simp only [regularizedQuadraticLFunctionProduct, quadraticLFunctionProduct,
    regularizedRiemannZeta_apply_of_ne_one s hs, mul_assoc]

/--
@isnad1 id=eq.1h4v.s6.b53d8106d23f from=translated src=- shape=bd2d9958 vocab=c693a1e6
-/
theorem regularizedQuadraticLFunctionProduct_eq_mul_LSeries {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    regularizedQuadraticLFunctionProduct χ₁ χ₂ s =
      (s - 1) * LSeries (quadraticProductCoefficients χ₁ χ₂) s := by
  have hs1 : s ≠ 1 := by
    intro heq
    simp only [heq, Complex.one_re, lt_self_iff_false] at hs
  rw [regularizedQuadraticLFunctionProduct_eq χ₁ χ₂ s hs1,
    LSeries_quadraticProductCoefficients χ₁ χ₂ hs]
  rfl

/-- Qualitative nonvanishing makes this a nonzero regularized value;
this theorem provides no uniform lower bound.
@isnad1 id=ne.3h3v.s8.4f817c81155c from=translated src=- shape=75847387 vocab=831fd965
-/
theorem regularizedQuadraticLFunctionProduct_one_ne_zero {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1)
    (hχ₁₂ : χ₁ * χ₂ ≠ 1) :
    regularizedQuadraticLFunctionProduct χ₁ χ₂ 1 ≠ 0 := by
  rw [regularizedQuadraticLFunctionProduct_one]
  exact mul_ne_zero (mul_ne_zero (DirichletCharacter.LFunction_apply_one_ne_zero hχ₁)
    (DirichletCharacter.LFunction_apply_one_ne_zero hχ₂))
    (DirichletCharacter.LFunction_apply_one_ne_zero hχ₁₂)

/-- The regularized value is the actual limit at the simple zeta pole.
@isnad1 id=tendsto.3h3v.s8.0ea091586e5b from=translated src=- shape=0b9a0570 vocab=c49e43d8
-/
theorem tendsto_mul_quadraticLFunctionProduct_at_one {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1)
    (hχ₁₂ : χ₁ * χ₂ ≠ 1) :
    Tendsto (fun s : ℂ => (s - 1) * quadraticLFunctionProduct χ₁ χ₂ s)
      (𝓝[≠] (1 : ℂ))
      (𝓝 (DirichletCharacter.LFunction χ₁ 1 * DirichletCharacter.LFunction χ₂ 1 *
        DirichletCharacter.LFunction (χ₁ * χ₂) 1)) := by
  have hreg : Tendsto (regularizedQuadraticLFunctionProduct χ₁ χ₂) (𝓝 (1 : ℂ))
      (𝓝 (DirichletCharacter.LFunction χ₁ 1 * DirichletCharacter.LFunction χ₂ 1 *
        DirichletCharacter.LFunction (χ₁ * χ₂) 1)) := by
    simpa only [regularizedQuadraticLFunctionProduct_one] using
      (differentiable_regularizedQuadraticLFunctionProduct χ₁ χ₂ hχ₁ hχ₂ hχ₁₂).continuous.tendsto 1
  apply (hreg.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact regularizedQuadraticLFunctionProduct_eq χ₁ χ₂ s hs

end TwinPrime.Analytic
