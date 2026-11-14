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
absolute convergence. No quadratic or nonprincipal assumptions are needed.-/
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
product on the half-plane of absolute convergence.-/
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

/-- The algebra only needs the first character to have square one.-/
theorem quadratic_character_mul_ne_one_of_ne {q : ℕ}
    (χ₁ χ₂ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1) (hne : χ₁ ≠ χ₂) :
    χ₁ * χ₂ ≠ 1 := by
  intro hmul
  have hinv : χ₁⁻¹ = χ₁ := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hχ₁)
  exact hne (hinv.symm.trans (mul_eq_one_iff_inv_eq.mp hmul))

theorem differentiable_regularizedQuadraticLFunctionProduct {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1)
    (hχ₁₂ : χ₁ * χ₂ ≠ 1) :
    Differentiable ℂ (regularizedQuadraticLFunctionProduct χ₁ χ₂) := by
  exact ((differentiable_regularizedRiemannZeta.mul
    (DirichletCharacter.differentiable_LFunction hχ₁)).mul
    (DirichletCharacter.differentiable_LFunction hχ₂)).mul
    (DirichletCharacter.differentiable_LFunction hχ₁₂)

theorem differentiable_regularizedQuadraticLFunctionProduct_of_quadratic {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1)
    (hsq : χ₁ ^ 2 = 1) (hne : χ₁ ≠ χ₂) :
    Differentiable ℂ (regularizedQuadraticLFunctionProduct χ₁ χ₂) :=
  differentiable_regularizedQuadraticLFunctionProduct χ₁ χ₂ hχ₁ hχ₂
    (quadratic_character_mul_ne_one_of_ne χ₁ χ₂ hsq hne)

@[simp] theorem regularizedQuadraticLFunctionProduct_one {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) :
    regularizedQuadraticLFunctionProduct χ₁ χ₂ 1 =
      DirichletCharacter.LFunction χ₁ 1 * DirichletCharacter.LFunction χ₂ 1 *
        DirichletCharacter.LFunction (χ₁ * χ₂) 1 := by
  simp [regularizedQuadraticLFunctionProduct]

theorem regularizedQuadraticLFunctionProduct_eq {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) (s : ℂ) (hs : s ≠ 1) :
    regularizedQuadraticLFunctionProduct χ₁ χ₂ s =
      (s - 1) * quadraticLFunctionProduct χ₁ χ₂ s := by
  simp only [regularizedQuadraticLFunctionProduct, quadraticLFunctionProduct,
    regularizedRiemannZeta_apply_of_ne_one s hs, mul_assoc]

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
this theorem provides no uniform lower bound.-/
theorem regularizedQuadraticLFunctionProduct_one_ne_zero {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1)
    (hχ₁₂ : χ₁ * χ₂ ≠ 1) :
    regularizedQuadraticLFunctionProduct χ₁ χ₂ 1 ≠ 0 := by
  rw [regularizedQuadraticLFunctionProduct_one]
  exact mul_ne_zero (mul_ne_zero (DirichletCharacter.LFunction_apply_one_ne_zero hχ₁)
    (DirichletCharacter.LFunction_apply_one_ne_zero hχ₂))
    (DirichletCharacter.LFunction_apply_one_ne_zero hχ₁₂)

/-- The regularized value is the actual limit at the simple zeta pole.-/
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
