import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_ArchParam
import Tengoku.Seed.Analysis.MellinTransform
import Tengoku.FltAnthropic.Theorems.Thm_LanglandsTunnell_mellin_mulConvGaussian_eq_archFactor_principal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_principal_profile_exists_ne_zero.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_principal_profile_exists_ne_zero

set_option autoImplicit false
open scoped Real
open MeasureTheory Set
open LanglandsTunnell

/--
@isnad1 id=ex.1h6v.s8.3267437a3ec9 from=translated src=- shape=e4970298 vocab=3db9e743
-/
theorem solution (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2)
    (c : ℂ) (f : ℝ → ℂ)
    (hf : ∀ y : ℝ, f y = (y : ℂ) ^ (1 / 2 - c) *
      ((4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
        ((t : ℂ) ^ (u₁ + signShift a₁) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
          (((y / t : ℝ) : ℂ) ^ (u₂ + signShift a₂) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ))) :
    ∃ y : ℝ, 0 < y ∧ f y ≠ 0 := by
  by_contra hcon
  push Not at hcon

  have hW : ∀ y : ℝ, 0 < y → ((4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
      ((t : ℂ) ^ (u₁ + signShift a₁) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
        (((y / t : ℝ) : ℂ) ^ (u₂ + signShift a₂) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ)) = 0 := by
    intro y hy
    have h := hcon y hy
    rw [hf y] at h
    rcases mul_eq_zero.1 h with h0 | h0
    · exfalso
      rw [Complex.cpow_eq_zero_iff] at h0
      exact Complex.ofReal_ne_zero.2 hy.ne' h0.1
    · exact h0

  set σ : ℝ := 1 + |(u₁ + signShift a₁).re| + |(u₂ + signShift a₂).re| with hσ
  have h₁ : 0 < ((σ : ℂ) + (u₁ + signShift a₁)).re := by
    rw [Complex.add_re, Complex.ofReal_re, hσ]
    linarith [neg_abs_le (u₁ + signShift a₁).re, abs_nonneg (u₂ + signShift a₂).re]
  have h₂ : 0 < ((σ : ℂ) + (u₂ + signShift a₂)).re := by
    rw [Complex.add_re, Complex.ofReal_re, hσ]
    linarith [neg_abs_le (u₂ + signShift a₂).re, abs_nonneg (u₁ + signShift a₁).re]
  have hid := LanglandsTunnell.mellin_mulConvGaussian_eq_archFactor_principal u₁ a₁ u₂ a₂ σ h₁ h₂

  have hL : mellin (fun y : ℝ => (4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
        ((t : ℂ) ^ (u₁ + signShift a₁) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
          (((y / t : ℝ) : ℂ) ^ (u₂ + signShift a₂) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ))
      (σ : ℂ) = 0 := by
    simp only [mellin]
    refine (setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_).trans (integral_zero _ _)
    have hy : (0 : ℝ) < y := hy
    simp only [hW y hy, smul_zero]

  have hR : (RealArchParam.principal u₁ a₁ u₂ a₂).archFactor (σ : ℂ) ≠ 0 := by
    simp only [RealArchParam.archFactor, RealArchParam.gammaR, RealArchParam.gammaC, Multiset.map_zero,
      Multiset.prod_zero, mul_one, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.prod_cons, Multiset.prod_singleton]
    exact mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos h₁) (Complex.Gammaℝ_ne_zero_of_re_pos h₂)
  exact hR (hL ▸ hid).symm
