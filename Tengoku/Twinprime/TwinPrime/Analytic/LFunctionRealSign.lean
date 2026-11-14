import Tengoku.Twinprime.TwinPrime.Analytic.LFunctionConjugateZeros
import Tengoku.Twinprime.TwinPrime.Analytic.LFunctionLowerBound
import Tengoku.Twinprime.TwinPrime.Analytic.ZetaRealTruncation
import Tengoku.Twinprime.TwinPrime.Analytic.QuadraticProductLSeries
import Tengoku.Seed.Topology.Order.IntermediateValue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Real signs below one under explicit zero exclusions

Quadratic nonprincipal characters have real L-values on the real axis.
Continuity and the positive real part at two determine their sign on an
explicit zero-free real interval. The zeta truncation at one gives a negative
real part just below its pole. No zero-free interval is inferred from a small
value or assumed implicitly.
-/

noncomputable section

open Set
open scoped ComplexConjugate

namespace TwinPrime.Analytic

/--
@isnad1 id=eq.2h3v.s7.1994812f0835 from=translated src=- shape=ff56553e vocab=11f2f4cf
-/
theorem LFunction_real_im_eq_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hsq : χ ^ 2 = 1) (u : ℝ) :
    (DirichletCharacter.LFunction χ (u : ℂ)).im = 0 := by
  have h := congrArg Complex.im (LFunction_conj_of_sq_eq_one χ hχ hsq (u : ℂ))
  simp only [Complex.conj_ofReal, Complex.conj_im] at h
  linarith

/--
@isnad1 id=eq.2h3v.s7.f1fbdb93d076 from=translated src=- shape=6f25aff8 vocab=32687145
-/
theorem LFunction_real_eq_ofReal_re {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hsq : χ ^ 2 = 1) (u : ℝ) :
    DirichletCharacter.LFunction χ (u : ℂ) =
      ((DirichletCharacter.LFunction χ (u : ℂ)).re : ℂ) := by
  apply Complex.ext
  · simp only [Complex.ofReal_re]
  · simpa only [Complex.ofReal_im] using LFunction_real_im_eq_zero χ hχ hsq u

/--
@isnad1 id=le.0h2v.s5.d229298db53c from=translated src=- shape=f7ffb8ea vocab=baa1e33d
-/
theorem one_quarter_le_LFunction_two_re {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    1 / 4 ≤ (DirichletCharacter.LFunction χ 2).re := by
  have h := norm_LFunction_sub_one_le χ 2 (by norm_num)
  have hre := (abs_le.mp ((Complex.abs_re_le_norm
    (DirichletCharacter.LFunction χ 2 - 1)).trans h)).1
  simp only [Complex.sub_re, Complex.one_re] at hre
  linarith

/-- Positivity follows from the supplied real zero exclusion and the known
nonvanishing at and to the right of one. The lower endpoint may be any real
number at most one; no condition on negative real arguments is suppressed.
@isnad1 id=lt.4h3v.s8.7b9294be2c9e from=translated src=- shape=62ae5507 vocab=2a56f1e8
-/
theorem LFunction_real_re_pos_of_no_zeros {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hsq : χ ^ 2 = 1)
    (β : ℝ) (hβ1 : β ≤ 1)
    (hno : ∀ u ∈ Ico β 1, DirichletCharacter.LFunction χ (u : ℂ) ≠ 0) :
    0 < (DirichletCharacter.LFunction χ (β : ℂ)).re := by
  let g : ℝ → ℝ := fun u => (DirichletCharacter.LFunction χ (u : ℂ)).re
  have hg : Continuous g := Complex.continuous_re.comp
    ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp Complex.continuous_ofReal)
  have htwo : 0 < g 2 := by
    have h := one_quarter_le_LFunction_two_re χ
    dsimp [g]
    norm_cast
    linarith
  by_contra hpos
  have hβ : g β ≤ 0 := le_of_not_gt hpos
  obtain ⟨u, hu, hgu⟩ := intermediate_value_Icc (by linarith : β ≤ 2) hg.continuousOn
    (show (0 : ℝ) ∈ Icc (g β) (g 2) from ⟨hβ, htwo.le⟩)
  have hzero : DirichletCharacter.LFunction χ (u : ℂ) = 0 := by
    apply Complex.ext
    · simpa only [g, Complex.zero_re] using hgu
    · simpa only [Complex.zero_im] using LFunction_real_im_eq_zero χ hχ hsq u
  by_cases hu1 : u < 1
  · exact hno u ⟨hu.1, hu1⟩ hzero
  · exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
      (by simp only [Complex.ofReal_re]; linarith)) hzero

/-- Truncation at `N=1` retains the negative pole term just below one.
@isnad1 id=lt.2h1v.s5.114d795970ae from=translated src=- shape=6a3344be vocab=b4f0db53
-/
theorem riemannZeta_re_neg_of_nineteen_twentieths_le (β : ℝ)
    (hβ : 19 / 20 ≤ β) (hβ1 : β < 1) : (riemannZeta (β : ℂ)).re < 0 := by
  have hβ0 : 0 < β := by linarith
  have herr := norm_zeta_real_sum_sub_zeta_sub_main_le 1 (by norm_num) β hβ0 hβ1
  have hnorm : ‖(1 : ℂ) - riemannZeta (β : ℂ) - 1 / (1 - (β : ℂ))‖ ≤ 1 := by
    simpa using herr
  have hfrac : (1 : ℂ) / (1 - (β : ℂ)) = ((1 / (1 - β) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hfrac] at hnorm
  have hre := (abs_le.mp ((Complex.abs_re_le_norm
    ((1 : ℂ) - riemannZeta (β : ℂ) - ((1 / (1 - β) : ℝ) : ℂ))).trans hnorm)).1
  simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re] at hre
  have hpole : (2 : ℝ) < 1 / (1 - β) :=
    (lt_div_iff₀ (sub_pos.mpr hβ1)).mpr (by linarith)
  linarith

/-- If all three real character factors have no zeros between `β` and one,
the actual four-factor product has negative real part at `β`.
@isnad1 id=lt.10h4v.s9.97141241e914 from=translated src=- shape=46acf135 vocab=4b0d35c2
-/
theorem quadraticLFunctionProduct_real_re_neg_of_no_zeros
    {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hχ₁₂ : χ₁ * χ₂ ≠ 1)
    (hsq₁ : χ₁ ^ 2 = 1) (hsq₂ : χ₂ ^ 2 = 1)
    (β : ℝ) (hβ : 19 / 20 ≤ β) (hβ1 : β < 1)
    (hno₁ : ∀ u ∈ Ico β 1, DirichletCharacter.LFunction χ₁ (u : ℂ) ≠ 0)
    (hno₂ : ∀ u ∈ Ico β 1, DirichletCharacter.LFunction χ₂ (u : ℂ) ≠ 0)
    (hno₁₂ : ∀ u ∈ Ico β 1, DirichletCharacter.LFunction (χ₁ * χ₂) (u : ℂ) ≠ 0) :
    (quadraticLFunctionProduct χ₁ χ₂ (β : ℂ)).re < 0 := by
  have hsq₁₂ : (χ₁ * χ₂) ^ 2 = 1 := by rw [mul_pow, hsq₁, hsq₂, mul_one]
  have h₁ := LFunction_real_re_pos_of_no_zeros χ₁ hχ₁ hsq₁ β hβ1.le hno₁
  have h₂ := LFunction_real_re_pos_of_no_zeros χ₂ hχ₂ hsq₂ β hβ1.le hno₂
  have h₁₂ := LFunction_real_re_pos_of_no_zeros (χ₁ * χ₂) hχ₁₂ hsq₁₂ β hβ1.le hno₁₂
  have hz := riemannZeta_re_neg_of_nineteen_twentieths_le β hβ hβ1
  unfold quadraticLFunctionProduct
  rw [LFunction_real_eq_ofReal_re χ₁ hχ₁ hsq₁ β,
    LFunction_real_eq_ofReal_re χ₂ hχ₂ hsq₂ β,
    LFunction_real_eq_ofReal_re (χ₁ * χ₂) hχ₁₂ hsq₁₂ β]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hz h₁) h₂) h₁₂

end TwinPrime.Analytic
