import Tengoku.Twinprime.TwinPrime.Analytic.MellinRampKernel
import Tengoku.Twinprime.TwinPrime.Analytic.LFunctionNonquadraticZeroFree

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Quantitative tails for Mellin inversion

A square-decay majorant gives a `2C/H` error when an integrable vertical
integral is truncated to `[-H,H]`. The actual Mangoldt Dirichlet mass also
has the explicit bound needed when the right line approaches one.
-/

noncomputable section

open MeasureTheory Set Complex

namespace TwinPrime.Analytic

theorem norm_integral_Ioi_le_of_inv_sq_bound (g : ℝ → ℂ) (H C : ℝ)
    (hH : 0 < H) (hbound : ∀ t : ℝ, H < t → ‖g t‖ ≤ C / t ^ 2) :
    ‖∫ t : ℝ in Ioi H, g t‖ ≤ C / H := by
  have hi : IntegrableOn (fun t : ℝ => C * t ^ (-2 : ℝ)) (Ioi H) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hH).const_mul C
  calc
    _ ≤ ∫ t : ℝ in Ioi H, C * t ^ (-2 : ℝ) := by
      apply MeasureTheory.norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have he : C * t ^ (-2 : ℝ) = C / t ^ 2 := by
        rw [Real.rpow_neg (lt_trans hH ht).le, Real.rpow_two, div_eq_mul_inv]
      rw [he]
      exact hbound t ht
    _ = C / H := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hH]
      norm_num [Real.rpow_neg_one]
      ring

/-- Both tails are retained, with no unproved improper-integral limit.-/
theorem norm_integral_sub_intervalIntegral_le_of_inv_sq_bound
    (g : ℝ → ℂ) (hg : Integrable g) (H C : ℝ) (hH : 0 < H)
    (hbound : ∀ t : ℝ, H ≤ |t| → ‖g t‖ ≤ C / t ^ 2) :
    ‖(∫ t : ℝ, g t) - ∫ t : ℝ in -H..H, g t‖ ≤ 2 * C / H := by
  have hright : ‖∫ t : ℝ in Ioi H, g t‖ ≤ C / H :=
    norm_integral_Ioi_le_of_inv_sq_bound g H C hH (fun t ht =>
      hbound t (by rw [abs_of_pos (lt_trans hH ht)]; exact ht.le))
  have hleft : ‖∫ t : ℝ in Iic (-H), g t‖ ≤ C / H := by
    rw [← integral_comp_neg_Ioi H g]
    apply norm_integral_Ioi_le_of_inv_sq_bound (fun t => g (-t)) H C hH
    intro t ht
    have hb := hbound (-t) (by rw [abs_neg, abs_of_pos (lt_trans hH ht)]; exact ht.le)
    simpa only [neg_sq] using hb
  have hsplit := intervalIntegral.integral_Iic_add_Ioi
    (b := H) hg.integrableOn hg.integrableOn
  have hmiddle := intervalIntegral.integral_Iic_sub_Iic
    (a := -H) (b := H) hg.integrableOn hg.integrableOn
  have he : (∫ t : ℝ, g t) - ∫ t : ℝ in -H..H, g t =
      (∫ t : ℝ in Iic (-H), g t) + (∫ t : ℝ in Ioi H, g t) := by
    linear_combination -hsplit + hmiddle
  rw [he]
  have ht := norm_add_le (∫ t : ℝ in Iic (-H), g t) (∫ t : ℝ in Ioi H, g t)
  calc
    _ ≤ C / H + C / H := ht.trans (_root_.add_le_add hleft hright)
    _ = _ := by ring

theorem norm_mellinRampKernel_le_inv_im_sq (s : ℂ) (hs : s.im ≠ 0) :
    ‖mellinRampKernel s‖ ≤ 1 / s.im ^ 2 := by
  have h1 := Complex.abs_im_le_norm s
  have h2 := Complex.abs_im_le_norm (s + 1)
  simp only [add_im, one_im, add_zero] at h2
  have hprod : s.im ^ 2 ≤ ‖s‖ * ‖s + 1‖ := by
    have hm := mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
    nlinarith [sq_abs s.im]
  rw [mellinRampKernel, norm_div, norm_one, norm_mul]
  exact one_div_le_one_div_of_le (sq_pos_of_ne_zero hs) hprod

theorem mangoldtDirichletMass_le_pole_add_forty (c : ℝ)
    (hc : 1 < c) (hcu : c ≤ 9 / 8) :
    mangoldtDirichletMass c ≤ 1 / (c - 1) + 40 := by
  have h := neg_zeta_logDerivative_real_le_pole_add_forty c hc hcu
  rwa [neg_zeta_logDerivative_eq_mass hc, Complex.ofReal_re] at h

theorem norm_mangoldt_mellin_integrand_le_inv_sq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (x c t : ℝ) (hx : 0 < x) (hc : 1 < c) (ht : t ≠ 0) :
    ‖(x : ℂ) ^ ((c : ℂ) + t * I) *
        (-deriv (DirichletCharacter.LFunction χ) ((c : ℂ) + t * I) /
          DirichletCharacter.LFunction χ ((c : ℂ) + t * I)) *
        mellinRampKernel ((c : ℂ) + t * I)‖ ≤
      x ^ c * mangoldtDirichletMass c / t ^ 2 := by
  let s : ℂ := (c : ℂ) + t * I
  have hsr : s.re = c := by simp [s]
  have hsi : s.im = t := by simp [s]
  have hmass := norm_twist_vonMangoldt_LSeries_le χ (s := s) (by rwa [hsr])
  rw [← neg_LFunction_logDerivative_eq_twist χ (by rwa [hsr]), hsr] at hmass
  have hkernel := norm_mellinRampKernel_le_inv_im_sq s (by rwa [hsi])
  rw [hsi] at hkernel
  change ‖(x : ℂ) ^ s * (-deriv (DirichletCharacter.LFunction χ) s /
    DirichletCharacter.LFunction χ s) * mellinRampKernel s‖ ≤ _
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, hsr]
  calc
    _ ≤ (x ^ c * mangoldtDirichletMass c) * (1 / t ^ 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hmass (Real.rpow_nonneg hx.le _)) hkernel
        (norm_nonneg _) (mul_nonneg (Real.rpow_nonneg hx.le _) (mangoldtDirichletMass_nonneg c))
    _ = _ := by ring

end TwinPrime.Analytic
