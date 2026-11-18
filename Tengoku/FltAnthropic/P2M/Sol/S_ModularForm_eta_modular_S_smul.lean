import Tengoku.Seed.NumberTheory.ModularForms.Discriminant
import Tengoku.Seed.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularForm_eta_modular_S_smul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularForm_eta_modular_S_smul

set_option autoImplicit false

noncomputable section

open Complex ModularGroup

open UpperHalfPlane hiding I

open scoped ModularForm MatrixGroups Real

namespace DedekindEtaLaw

lemma sqrt_sq (a : ℂ) : Complex.sqrt a ^ 2 = a := by
  have h := cpow_nat_inv_pow a two_ne_zero
  rw [Complex.sqrt]
  norm_num at h ⊢
  exact h

lemma sqrt_re (a : ℂ) : (Complex.sqrt a).re = √((‖a‖ + a.re) / 2) := by
  rw [Complex.sqrt]; exact cpow_inv_two_re a

lemma sqrt_re_pos {a : ℂ} (ha : 0 < a.re) : 0 < (Complex.sqrt a).re := by
  rw [sqrt_re]
  apply Real.sqrt_pos_of_pos
  have := norm_nonneg a
  linarith

lemma eq_of_sq_eq_sq_of_re_pos {s t : ℂ} (h : s ^ 2 = t ^ 2) (hs : 0 < s.re) (ht : 0 < t.re) :
    s = t := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
  · exact h
  · exfalso
    rw [h, neg_re] at hs
    linarith

lemma neg_I_mul_re (ζ : ℂ) : (-I * ζ).re = ζ.im := by simp

lemma sqrt_I_inv : (Complex.sqrt I)⁻¹ = Complex.sqrt (-I) := by
  rw [Complex.sqrt_neg_I, Complex.sqrt_I]
  have hs : (√(2⁻¹) : ℝ) ^ 2 = 2⁻¹ := Real.sq_sqrt (by norm_num)
  refine inv_eq_of_mul_eq_one_right ?_
  rw [show (((√(2⁻¹) : ℝ) : ℂ) * (1 + I)) * (((√(2⁻¹) : ℝ) : ℂ) * (1 - I))
      = (((√(2⁻¹) : ℝ) ^ 2 : ℝ) : ℂ) * (1 - I ^ 2) by push_cast; ring, hs, I_sq]
  push_cast
  ring

lemma sqrt_I_inv_mul_sqrt (z : ℍ) : (Complex.sqrt I)⁻¹ * Complex.sqrt (z : ℂ) = Complex.sqrt (-I * z) := by
  rw [sqrt_I_inv]
  apply eq_of_sq_eq_sq_of_re_pos
  · rw [mul_pow, sqrt_sq, sqrt_sq, sqrt_sq]
  ·
    rw [Complex.sqrt_neg_I, mul_assoc, re_ofReal_mul]
    have hz : Complex.sqrt (z : ℂ) = √((‖(z : ℂ)‖ + (z : ℂ).re) / 2) + √((‖(z : ℂ)‖ - (z : ℂ).re) / 2) * I := by
      rw [Complex.sqrt_eq_real_add_ite, ite_eq_left (by exact_mod_cast z.2.le), one_mul]
    have hx : 0 ≤ √((‖(z : ℂ)‖ + (z : ℂ).re) / 2) := Real.sqrt_nonneg _
    have hy : 0 < √((‖(z : ℂ)‖ - (z : ℂ).re) / 2) := by
      apply Real.sqrt_pos_of_pos
      have h1 : (z : ℂ).re < ‖(z : ℂ)‖ := by
        refine lt_of_le_of_ne (re_le_norm _) fun h => ?_
        have h0 : (z : ℂ).im = 0 := ((Complex.re_eq_norm).1 h).2.symm
        exact z.2.ne' (by simpa using h0)
      linarith
    have : ((1 - I) * Complex.sqrt (z : ℂ)).re
        = √((‖(z : ℂ)‖ + (z : ℂ).re) / 2) + √((‖(z : ℂ)‖ - (z : ℂ).re) / 2) := by
      rw [hz]; simp [mul_re, sub_re, sub_im]
    rw [this]
    exact mul_pos (Real.sqrt_pos_of_pos (by norm_num)) (by linarith)
  · exact sqrt_re_pos (by rw [neg_I_mul_re]; exact z.2)

lemma coe_S_smul (z : ℍ) : ((ModularGroup.S • z : ℍ) : ℂ) = -(z : ℂ)⁻¹ := by
  rw [modular_S_smul]; simp [inv_neg]

lemma eta_S_smul (z : ℍ) : η (((ModularGroup.S • z : ℍ) : ℂ)) = Complex.sqrt (-I * z) * η z := by
  have he : η (-(z : ℂ)⁻¹) = (Complex.sqrt I)⁻¹ * (Complex.sqrt z * η z) := by
    simpa [neg_div] using ModularForm.eta_comp_eq_csqrt_I_inv z.2
  rw [coe_S_smul, he, ← mul_assoc, sqrt_I_inv_mul_sqrt]

end DedekindEtaLaw

end

theorem solution (z : UpperHalfPlane) : ModularForm.eta ((ModularGroup.S • z : UpperHalfPlane) : ℂ) = Complex.sqrt (-Complex.I * z) * ModularForm.eta z :=
  DedekindEtaLaw.eta_S_smul z
