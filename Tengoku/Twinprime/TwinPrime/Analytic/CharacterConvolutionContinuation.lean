import Tengoku.Twinprime.TwinPrime.Analytic.PowerDirichletContinuation
import Tengoku.Twinprime.TwinPrime.Analytic.CharacterConvolutionPower
import Tengoku.Seed.NumberTheory.LSeries.Nonvanishing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ordered triple character convolution at one

Absolute convergence identifies the triple convolution with three actual
L-functions on `Re(s)>1`. A proved power bound for the coefficients then
gives ordered holomorphic continuation past one when all three characters
are nonprincipal. No primitivity or distribution hypothesis is used.
-/

noncomputable section

open Finset Filter
open scoped Topology

namespace TwinPrime.Analytic

/--
@isnad1 id=lseriess.1h3v.s6.260bc759710b from=translated src=- shape=9066a502 vocab=443d3bf7
-/
theorem LSeriesSummable_characterArithmeticFunction {q : ℕ}
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (toArithmeticFunction (χ ·)) s := by
  exact (LSeriesSummable_congr s fun hn =>
    (χ.apply_eq_toArithmeticFunction_apply hn).symm).mpr
      (χ.LSeriesSummable_of_one_lt_re hs)

/--
@isnad1 id=eq.1h3v.s6.f81d46a941ec from=translated src=- shape=ae7c0a84 vocab=714b7356
-/
theorem LSeries_characterArithmeticFunction {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeries (toArithmeticFunction (χ ·)) s = DirichletCharacter.LFunction χ s := by
  rw [χ.LFunction_eq_LSeries hs]
  exact LSeries_congr (fun hn => (χ.apply_eq_toArithmeticFunction_apply hn).symm) s

/--
@isnad1 id=lseriess.1h5v.s8.944da7bf0261 from=translated src=- shape=d1b2f3db vocab=727ca210
-/
theorem LSeriesSummable_three_character_convolution {q : ℕ}
    (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable ((toArithmeticFunction (χ₁ ·) * toArithmeticFunction (χ₂ ·) *
      toArithmeticFunction (χ₃ ·)) : ArithmeticFunction ℂ) s :=
  ArithmeticFunction.LSeriesSummable_mul
    (ArithmeticFunction.LSeriesSummable_mul (LSeriesSummable_characterArithmeticFunction χ₁ hs)
      (LSeriesSummable_characterArithmeticFunction χ₂ hs))
    (LSeriesSummable_characterArithmeticFunction χ₃ hs)

/-- The product is Dirichlet convolution, with the entire arithmetic-function
expression typed before coercion to a sequence.
@isnad1 id=eq.1h5v.s8.fe1b15ac16c1 from=translated src=- shape=ecddc75d vocab=9b710118
-/
theorem LSeries_three_character_convolution {q : ℕ} [NeZero q]
    (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeries ((toArithmeticFunction (χ₁ ·) * toArithmeticFunction (χ₂ ·) *
      toArithmeticFunction (χ₃ ·)) : ArithmeticFunction ℂ) s =
      DirichletCharacter.LFunction χ₁ s * DirichletCharacter.LFunction χ₂ s *
        DirichletCharacter.LFunction χ₃ s := by
  have h₁ := LSeriesSummable_characterArithmeticFunction χ₁ hs
  have h₂ := LSeriesSummable_characterArithmeticFunction χ₂ hs
  have h₃ := LSeriesSummable_characterArithmeticFunction χ₃ hs
  rw [ArithmeticFunction.LSeries_mul' (ArithmeticFunction.LSeriesSummable_mul h₁ h₂) h₃,
    ArithmeticFunction.LSeries_mul' h₁ h₂, LSeries_characterArithmeticFunction χ₁ hs,
    LSeries_characterArithmeticFunction χ₂ hs, LSeries_characterArithmeticFunction χ₃ hs]

/--
@isnad1 id=differen.3h4v.s8.6e09bb04c786 from=translated src=- shape=42d995f2 vocab=82761ebd
-/
theorem differentiable_threeLFunctionProduct {q : ℕ} [NeZero q]
    (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hχ₃ : χ₃ ≠ 1) :
    Differentiable ℂ (fun s => DirichletCharacter.LFunction χ₁ s *
      DirichletCharacter.LFunction χ₂ s * DirichletCharacter.LFunction χ₃ s) :=
  ((DirichletCharacter.differentiable_LFunction hχ₁).mul
    (DirichletCharacter.differentiable_LFunction hχ₂)).mul
    (DirichletCharacter.differentiable_LFunction hχ₃)

/--
@isnad1 id=eq.0h2v.s5.dfeb72d4b45f from=translated src=- shape=8924a20c vocab=bcf8b4e7
-/
theorem powerDirichletPartialSum_one_eq_reciprocal (a : ℕ → ℂ) (M : ℕ) :
    powerDirichletPartialSum a 1 M = ∑ n ∈ Ioc 0 M, a n / (n : ℂ) := by
  simp only [powerDirichletPartialSum, Complex.cpow_neg, Complex.cpow_one,
    div_eq_mul_inv, mul_comm]

private theorem three_character_convolution_limit_eqOn_of_power_bound
    {q : ℕ} [NeZero q] (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hχ₃ : χ₃ ≠ 1)
    (hA : ∀ N : ℕ, ‖∑ n ∈ Ioc 0 N,
      ((toArithmeticFunction (χ₁ ·) * toArithmeticFunction (χ₂ ·) *
        toArithmeticFunction (χ₃ ·)) : ArithmeticFunction ℂ) n‖ ≤
      (130 * (q : ℝ) ^ 2) * (N : ℝ) ^ (3 / 4 : ℝ)) :
    Set.EqOn (powerDirichletLimit ((toArithmeticFunction (χ₁ ·) *
      toArithmeticFunction (χ₂ ·) * toArithmeticFunction (χ₃ ·)) : ArithmeticFunction ℂ))
      (fun s => DirichletCharacter.LFunction χ₁ s * DirichletCharacter.LFunction χ₂ s *
        DirichletCharacter.LFunction χ₃ s) {s : ℂ | (3 / 4 : ℝ) < s.re} := by
  apply powerDirichletLimit_eqOn_of_LSeries_right (3 / 4) (by norm_num) _
    (130 * (q : ℝ) ^ 2) (by positivity) hA _
    (differentiable_threeLFunctionProduct χ₁ χ₂ χ₃ hχ₁ hχ₂ hχ₃).differentiableOn
  · intro s hs
    exact LSeriesSummable_three_character_convolution χ₁ χ₂ χ₃
      ((le_max_right (3 / 4 : ℝ) 1).trans_lt hs)
  · intro s hs
    exact LSeries_three_character_convolution χ₁ χ₂ χ₃
      ((le_max_right (3 / 4 : ℝ) 1).trans_lt hs)

/-- The prefix-power estimate is discharged by actual nonprincipal-character
cancellation. No convergence premise is assumed on the enlarged half-plane.
@isnad1 id=eqon.3h4v.s8.03e5788df839 from=translated src=- shape=079faa7b vocab=d262e99e
-/
theorem powerDirichletLimit_three_character_convolution_eqOn
    {q : ℕ} [NeZero q] (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hχ₃ : χ₃ ≠ 1) :
    Set.EqOn (powerDirichletLimit ((toArithmeticFunction (χ₁ ·) *
      toArithmeticFunction (χ₂ ·) * toArithmeticFunction (χ₃ ·)) : ArithmeticFunction ℂ))
      (fun s => DirichletCharacter.LFunction χ₁ s * DirichletCharacter.LFunction χ₂ s *
        DirichletCharacter.LFunction χ₃ s) {s : ℂ | (3 / 4 : ℝ) < s.re} :=
  three_character_convolution_limit_eqOn_of_power_bound χ₁ χ₂ χ₃ hχ₁ hχ₂ hχ₃
    (norm_three_character_convolution_prefix_le_power χ₁ χ₂ χ₃ hχ₁ hχ₂ hχ₃)

/--
@isnad1 id=tendstol.3h4v.s9.3761b228fdd6 from=translated src=- shape=298e9cfa vocab=3af73084
-/
theorem tendstoLocallyUniformlyOn_three_character_convolution_LFunctions
    {q : ℕ} [NeZero q] (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hχ₃ : χ₃ ≠ 1) :
    TendstoLocallyUniformlyOn (fun N s => powerDirichletPartialSum
      ((toArithmeticFunction (χ₁ ·) * toArithmeticFunction (χ₂ ·) *
        toArithmeticFunction (χ₃ ·)) : ArithmeticFunction ℂ) s N)
      (fun s => DirichletCharacter.LFunction χ₁ s * DirichletCharacter.LFunction χ₂ s *
        DirichletCharacter.LFunction χ₃ s) atTop {s : ℂ | (3 / 4 : ℝ) < s.re} :=
  (tendstoLocallyUniformlyOn_powerDirichletPartialSum_limit (3 / 4) (by norm_num) _
    (130 * (q : ℝ) ^ 2) (by positivity)
    (norm_three_character_convolution_prefix_le_power χ₁ χ₂ χ₃ hχ₁ hχ₂ hχ₃)).congr_right
    (powerDirichletLimit_three_character_convolution_eqOn χ₁ χ₂ χ₃ hχ₁ hχ₂ hχ₃)

/--
@isnad1 id=tendsto.4h5v.s8.311800b222bc from=translated src=- shape=32be14bf vocab=b3ab3f65
-/
theorem tendsto_three_character_convolution_partialSum_LFunctions
    {q : ℕ} [NeZero q] (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hχ₃ : χ₃ ≠ 1)
    (s : ℂ) (hs : (3 / 4 : ℝ) < s.re) :
    Tendsto (powerDirichletPartialSum ((toArithmeticFunction (χ₁ ·) *
      toArithmeticFunction (χ₂ ·) * toArithmeticFunction (χ₃ ·)) : ArithmeticFunction ℂ) s)
      atTop (𝓝 (DirichletCharacter.LFunction χ₁ s * DirichletCharacter.LFunction χ₂ s *
        DirichletCharacter.LFunction χ₃ s)) := by
  have heq := powerDirichletLimit_three_character_convolution_eqOn χ₁ χ₂ χ₃ hχ₁ hχ₂ hχ₃ hs
  dsimp only at heq
  rw [← heq]
  exact tendsto_powerDirichletPartialSum_limit (3 / 4) (by norm_num) _
    (130 * (q : ℝ) ^ 2) (by positivity)
    (norm_three_character_convolution_prefix_le_power χ₁ χ₂ χ₃ hχ₁ hχ₂ hχ₃) s hs

/--
@isnad1 id=le.5h6v.s9.b6a44931bb6b from=translated src=- shape=405f8796 vocab=635c950d
-/
theorem norm_threeLFunctionProduct_sub_partialSum_le
    {q : ℕ} [NeZero q] (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hχ₃ : χ₃ ≠ 1)
    (M : ℕ) (hM : 1 ≤ M) (s : ℂ) (hs : (3 / 4 : ℝ) < s.re) :
    ‖DirichletCharacter.LFunction χ₁ s * DirichletCharacter.LFunction χ₂ s *
        DirichletCharacter.LFunction χ₃ s - powerDirichletPartialSum
      ((toArithmeticFunction (χ₁ ·) * toArithmeticFunction (χ₂ ·) *
        toArithmeticFunction (χ₃ ·)) : ArithmeticFunction ℂ) s M‖ ≤
      (260 * (q : ℝ) ^ 2) * (M : ℝ) ^ ((3 / 4 : ℝ) - s.re) *
        (1 + ‖s‖ / (s.re - (3 / 4 : ℝ))) := by
  have h := norm_sub_powerDirichletPartialSum_le_of_eqOn (3 / 4) (by norm_num) _
    (130 * (q : ℝ) ^ 2) (by positivity)
    (norm_three_character_convolution_prefix_le_power χ₁ χ₂ χ₃ hχ₁ hχ₂ hχ₃) _
    (powerDirichletLimit_three_character_convolution_eqOn χ₁ χ₂ χ₃ hχ₁ hχ₂ hχ₃) M hM s hs
  convert h using 1
  ring

/-- The reciprocal sums converge in their natural order to the actual product
at one. This does not assert absolute summability of the reciprocal series.
@isnad1 id=tendsto.3h4v.s8.3b2df98fdf55 from=translated src=- shape=d75e4a88 vocab=68221c1f
-/
theorem tendsto_three_character_convolution_reciprocal_sum
    {q : ℕ} [NeZero q] (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hχ₃ : χ₃ ≠ 1) :
    Tendsto (fun M : ℕ => ∑ n ∈ Ioc 0 M,
      ((toArithmeticFunction (χ₁ ·) * toArithmeticFunction (χ₂ ·) *
        toArithmeticFunction (χ₃ ·)) : ArithmeticFunction ℂ) n / (n : ℂ)) atTop
      (𝓝 (DirichletCharacter.LFunction χ₁ 1 * DirichletCharacter.LFunction χ₂ 1 *
        DirichletCharacter.LFunction χ₃ 1)) := by
  exact (tendsto_three_character_convolution_partialSum_LFunctions
    χ₁ χ₂ χ₃ hχ₁ hχ₂ hχ₃ 1 (by norm_num)).congr
    (fun M => powerDirichletPartialSum_one_eq_reciprocal _ M)

/-- A fully explicit tail bound at one for arbitrary nonprincipal factors.
@isnad1 id=le.4h5v.s9.4e06fbb70f20 from=translated src=- shape=4e986f3f vocab=dc92d286
-/
theorem norm_threeLFunctionProduct_one_sub_reciprocal_sum_le
    {q : ℕ} [NeZero q] (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hχ₃ : χ₃ ≠ 1)
    (M : ℕ) (hM : 1 ≤ M) :
    ‖DirichletCharacter.LFunction χ₁ 1 * DirichletCharacter.LFunction χ₂ 1 *
        DirichletCharacter.LFunction χ₃ 1 - ∑ n ∈ Ioc 0 M,
      ((toArithmeticFunction (χ₁ ·) * toArithmeticFunction (χ₂ ·) *
        toArithmeticFunction (χ₃ ·)) : ArithmeticFunction ℂ) n / (n : ℂ)‖ ≤
      1300 * (q : ℝ) ^ 2 * (M : ℝ) ^ (-(1 / 4 : ℝ)) := by
  have h := norm_threeLFunctionProduct_sub_partialSum_le χ₁ χ₂ χ₃ hχ₁ hχ₂ hχ₃ M hM 1 (by norm_num)
  rw [powerDirichletPartialSum_one_eq_reciprocal] at h
  have hexp : (3 / 4 : ℝ) - 1 = -(1 / 4 : ℝ) := by norm_num
  have hfactor : (1 : ℝ) + 1 / (1 - 3 / 4) = 5 := by norm_num
  simp only [Complex.one_re, norm_one, hexp, hfactor] at h
  convert h using 1
  ring

end TwinPrime.Analytic
