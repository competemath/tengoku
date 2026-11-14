import Tengoku.Twinprime.TwinPrime.Analytic.LocalLogDerivativeExpansion
import Tengoku.Twinprime.TwinPrime.Analytic.LFunctionLowerBound
import Tengoku.Twinprime.TwinPrime.Analytic.ZetaLogDerivative
import Tengoku.Seed.NumberTheory.LSeries.Nonvanishing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The local expansion of regularized zeta at every height

The actual zero divisor of the entire function `(s-1)ζ(s)` supplies the
local expansion. Qualitative nonvanishing gives the signs of its reciprocal
zero terms. The resulting one-sided bound for `-ζ'/ζ` retains the principal
pole at arbitrary height, without a quantitative zero-free assumption.
-/

noncomputable section

open Function Metric MeromorphicOn

namespace TwinPrime.Analytic

def localZetaZeroSum (c s : ℂ) : ℂ :=
  ∑ᶠ ρ, (divisor regularizedRiemannZeta (closedBall c (5 / 4)) ρ : ℂ) / (s - ρ)

def zetaLogBudget (t : ℝ) : ℝ :=
  (144 * (1 + Real.log 5 / Real.log (6 / 5))) *
    (1 + Real.log 16 + 2 * Real.log (‖(2 : ℂ) + Complex.I * t‖ + 2))

theorem zetaLogBudget_nonneg (t : ℝ) : 0 ≤ zetaLogBudget t := by
  have h5 : 0 ≤ Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
  have h65 : 0 ≤ Real.log (6 / 5 : ℝ) := Real.log_nonneg (by norm_num)
  have h16 : 0 ≤ Real.log (16 : ℝ) := Real.log_nonneg (by norm_num)
  have hH : 0 ≤ Real.log (‖(2 : ℂ) + Complex.I * t‖ + 2) :=
    Real.log_nonneg (by have := norm_nonneg ((2 : ℂ) + Complex.I * t); linarith)
  unfold zetaLogBudget
  positivity

/-- The explicit budget grows only logarithmically with the height.-/
theorem zetaLogBudget_le_log_abs (t : ℝ) :
    zetaLogBudget t ≤
      (144 * (1 + Real.log 5 / Real.log (6 / 5))) *
        (1 + Real.log 16 + 2 * Real.log (|t| + 4)) := by
  have hn : ‖(2 : ℂ) + Complex.I * t‖ ≤ |t| + 2 := by
    have h := norm_add_le (2 : ℂ) (Complex.I * t)
    norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs] at h
    linarith
  have hl : Real.log (‖(2 : ℂ) + Complex.I * t‖ + 2) ≤ Real.log (|t| + 4) :=
    Real.log_le_log (by positivity) (by linarith)
  have h5 : 0 ≤ Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
  have h65 : 0 ≤ Real.log (6 / 5 : ℝ) := Real.log_nonneg (by norm_num)
  unfold zetaLogBudget
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith

theorem regularizedRiemannZeta_ne_zero_of_one_le_re (s : ℂ) (hs : 1 ≤ s.re) :
    regularizedRiemannZeta s ≠ 0 := by
  by_cases hs1 : s = 1
  · simp [hs1]
  · rw [regularizedRiemannZeta_apply_of_ne_one s hs1]
    exact mul_ne_zero (sub_ne_zero.mpr hs1) (riemannZeta_ne_zero_of_one_le_re hs)

theorem regularizedRiemannZeta_zero_re_lt_one (ρ : ℂ)
    (hρ : regularizedRiemannZeta ρ = 0) : ρ.re < 1 := by
  by_contra h
  exact regularizedRiemannZeta_ne_zero_of_one_le_re ρ (not_lt.mp h) hρ

theorem one_quarter_le_norm_regularizedRiemannZeta_center (c : ℂ) (hc : c.re = 2) :
    1 / 4 ≤ ‖regularizedRiemannZeta c‖ := by
  have hc1 : c ≠ 1 := by intro h; simp [h] at hc
  have hζ : 1 / 4 ≤ ‖riemannZeta c‖ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      one_quarter_le_norm_LFunction (1 : DirichletCharacter ℂ 1) c (by rw [hc])
  have hsub : 1 ≤ ‖c - 1‖ := by
    have h := Complex.re_le_norm (c - 1)
    simpa only [Complex.sub_re, Complex.one_re, hc, show (2 : ℝ) - 1 = 1 by norm_num] using h
  rw [regularizedRiemannZeta_apply_of_ne_one c hc1, norm_mul]
  calc
    _ ≤ ‖riemannZeta c‖ := hζ
    _ = 1 * ‖riemannZeta c‖ := (one_mul _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hsub (norm_nonneg _)

theorem regularizedZetaGrowthBudget_half_le (c : ℂ) :
    regularizedZetaGrowthBudget (1 / 2) (‖c‖ + 3 / 2) ≤ 4 * (‖c‖ + 2) ^ 2 := by
  unfold regularizedZetaGrowthBudget
  have hn := norm_nonneg c
  nlinarith [sq_nonneg ‖c‖]

theorem regularizedZeta_divisor_re_lt_one (K : Set ℂ) (ρ : ℂ)
    (hρ : divisor regularizedRiemannZeta K ρ ≠ 0) : ρ.re < 1 := by
  have ha := differentiable_regularizedRiemannZeta
  have hK : ρ ∈ K := (divisor regularizedRiemannZeta K).supportWithinDomain hρ
  by_contra hre
  have hn := regularizedRiemannZeta_ne_zero_of_one_le_re ρ (not_lt.mp hre)
  have ho := (ha.analyticAt ρ).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hn
  rw [divisor_apply (fun z _ => (ha.analyticAt z).meromorphicAt) hK, ho] at hρ
  simp at hρ

theorem regularizedZeta_divisor_term_re_nonneg (K : Set ℂ) (s ρ : ℂ) (hs : 1 < s.re) :
    0 ≤ ((divisor regularizedRiemannZeta K ρ : ℂ) / (s - ρ)).re := by
  by_cases hρ : divisor regularizedRiemannZeta K ρ = 0
  · simp [hρ]
  have hre := regularizedZeta_divisor_re_lt_one K ρ hρ
  have ha : AnalyticOnNhd ℂ regularizedRiemannZeta K :=
    fun z _ => differentiable_regularizedRiemannZeta.analyticAt z
  have hD : (0 : ℝ) ≤ divisor regularizedRiemannZeta K ρ := by
    exact_mod_cast ha.divisor_nonneg ρ
  simp only [Complex.div_re, Complex.intCast_re, Complex.intCast_im, Complex.sub_re,
    zero_mul, zero_div, add_zero]
  exact div_nonneg (mul_nonneg hD (by linarith)) (Complex.normSq_nonneg _)

theorem localZetaZeroTerm_hasFiniteSupport (c s : ℂ) :
    (fun ρ => (divisor regularizedRiemannZeta (closedBall c (5 / 4)) ρ : ℂ) /
      (s - ρ)).HasFiniteSupport := by
  apply ((divisor regularizedRiemannZeta (closedBall c (5 / 4))).finiteSupport
    (isCompact_closedBall c (5 / 4))).subset
  intro ρ hρ
  change divisor regularizedRiemannZeta (closedBall c (5 / 4)) ρ ≠ 0
  intro hD
  exact hρ (by simp [hD])

theorem localZetaZeroSum_re_nonneg (c s : ℂ) (hs : 1 < s.re) :
    0 ≤ (localZetaZeroSum c s).re := by
  have he : (localZetaZeroSum c s).re =
      ∑ᶠ ρ, ((divisor regularizedRiemannZeta (closedBall c (5 / 4)) ρ : ℂ) / (s - ρ)).re :=
    Complex.reAddGroupHom.map_finsum (localZetaZeroTerm_hasFiniteSupport c s)
  rw [he]
  exact finsum_nonneg (fun ρ => regularizedZeta_divisor_term_re_nonneg _ s ρ hs)

end TwinPrime.Analytic
