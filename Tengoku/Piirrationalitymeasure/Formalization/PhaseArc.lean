import Tengoku.Piirrationalitymeasure.Formalization.ContourPath

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Algebraic factorisations for the controlled arc, corresponding to (A.16).
-/

namespace PiIrrationality

noncomputable def arcDen (e lambda : ℝ) : ℂ :=
  1 - Complex.I * (e : ℂ) * (1 - (lambda : ℂ))

noncomputable def arcK (e lambda : ℝ) : ℂ :=
  (25 : ℂ) * (1 - (e : ℂ) ^ 2) - 50 * Complex.I * (e : ℂ) +
    (lambda : ℂ) *
      (25 * (e : ℂ) ^ 2 + 24 * (e : ℂ) + 7 +
        Complex.I * (18 * (e : ℂ) + 24))

noncomputable def arcL (e lambda : ℝ) : ℂ :=
  25 * arcDen e lambda - ((-3 : ℂ) + 4 * Complex.I) * (lambda : ℂ)

theorem arcDen_eq (e lambda : ℝ) :
    arcDen e lambda = 1 - Complex.I * (e : ℂ) * (1 - (lambda : ℂ)) := rfl

theorem arcDen_ne_zero (e lambda : ℝ) : arcDen e lambda ≠ 0 := by
  exact gammaPath_den_ne_zero e lambda

theorem gammaPath_eq_arc_fraction (e lambda : ℝ) :
    gammaPath e lambda = ((-3 : ℂ) + 4 * Complex.I) * (lambda : ℂ) /
      arcDen e lambda := by
  rfl

theorem arc_quadratic_factorization (e lambda : ℝ) :
    (gammaPath e lambda) ^ 2 + 6 * gammaPath e lambda + 25 =
      ((1 - (lambda : ℂ)) * arcK e lambda) / (arcDen e lambda) ^ 2 := by
  rw [gammaPath_eq_arc_fraction]
  have hden : arcDen e lambda ≠ 0 := arcDen_ne_zero e lambda
  unfold arcK
  field_simp [hden]
  simp [arcDen]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem arc_pole_factorization (e lambda : ℝ) :
    25 - gammaPath e lambda = arcL e lambda / arcDen e lambda := by
  rw [gammaPath_eq_arc_fraction]
  have hden : arcDen e lambda ≠ 0 := arcDen_ne_zero e lambda
  unfold arcL
  field_simp [hden]

theorem arcK_im (e lambda : ℝ) :
    (arcK e lambda).im = -50 * e + lambda * (18 * e + 24) := by
  unfold arcK
  simp [Complex.mul_im, pow_two]

theorem arcL_im (e lambda : ℝ) :
    (arcL e lambda).im = -25 * e * (1 - lambda) - 4 * lambda := by
  simp [arcL, arcDen]
  ring

def arcH (e lambda : ℝ) : ℝ :=
  625 * e ^ 4 + 1250 * e ^ 2 + 625 +
    (-1250 * e ^ 4 - 1200 * e ^ 3 - 900 * e ^ 2 - 1200 * e + 350) * lambda +
    (625 * e ^ 4 + 1200 * e ^ 3 + 1250 * e ^ 2 + 1200 * e + 625) * lambda ^ 2

def arcJ (e lambda : ℝ) : ℝ :=
  625 * e ^ 2 + 625 + (-1250 * e ^ 2 + 200 * e + 150) * lambda +
    (625 * e ^ 2 - 200 * e + 25) * lambda ^ 2

theorem arcK_normSq_eq (e lambda : ℝ) :
    Complex.normSq (arcK e lambda) = arcH e lambda := by
  rw [Complex.normSq_apply]
  simp [arcK, arcH, Complex.mul_re, Complex.mul_im, pow_two]
  ring

theorem arcL_normSq_eq (e lambda : ℝ) :
    Complex.normSq (arcL e lambda) = arcJ e lambda := by
  rw [Complex.normSq_apply]
  simp [arcL, arcDen, arcJ, Complex.mul_re, Complex.mul_im, pow_two]
  ring

theorem arcK_im_lt {e lambda : ℝ}
    (he : (9 : ℝ) / 10 < e) (hl0 : 0 ≤ lambda) (hl1 : lambda ≤ 1) :
    (arcK e lambda).im < -(24 : ℝ) / 5 := by
  rw [arcK_im]
  have hcoef : 0 ≤ 18 * e + 24 := by linarith
  have hmul : lambda * (18 * e + 24) ≤ 18 * e + 24 := by
    simpa [mul_comm] using (mul_le_of_le_one_right hcoef hl1)
  nlinarith

theorem arcL_im_le {e lambda : ℝ}
    (he : (9 : ℝ) / 10 < e) (hl0 : 0 ≤ lambda) (hl1 : lambda ≤ 1) :
    (arcL e lambda).im ≤ -4 := by
  rw [arcL_im]
  have he4 : 4 ≤ 25 * e := by linarith
  have hmul : 4 * (1 - lambda) ≤ 25 * e * (1 - lambda) := by
    exact mul_le_mul_of_nonneg_right he4 (sub_nonneg.mpr hl1)
  nlinarith

theorem arcK_normSq_gt {e lambda : ℝ}
    (he : (9 : ℝ) / 10 < e) (hl0 : 0 ≤ lambda) (hl1 : lambda ≤ 1) :
    (24 : ℝ) ^ 2 / 5 ^ 2 < Complex.normSq (arcK e lambda) := by
  have him := arcK_im_lt he hl0 hl1
  rw [Complex.normSq_apply]
  nlinarith [sq_nonneg (arcK e lambda).re]

theorem arcL_normSq_ge {e lambda : ℝ}
    (he : (9 : ℝ) / 10 < e) (hl0 : 0 ≤ lambda) (hl1 : lambda ≤ 1) :
    (16 : ℝ) ≤ Complex.normSq (arcL e lambda) := by
  have him := arcL_im_le he hl0 hl1
  rw [Complex.normSq_apply]
  nlinarith [sq_nonneg (arcL e lambda).re]

end PiIrrationality
