import Tengoku.Twinprime.TwinPrime.Analytic.MellinRampKernel
import Tengoku.Seed.Analysis.Complex.CauchyIntegral
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Deriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite rectangular shifts for the smoothed Mellin integrand

The vertical integrals use the upward real parameter. Cauchy--Goursat
identifies right minus left with `I` times bottom minus top. The estimates
are finite integral bounds and assume no prime-distribution statement.
-/

noncomputable section

open MeasureTheory Set Complex

namespace TwinPrime.Analytic

def mellinContourIntegrand (x : ℝ) (F : ℂ → ℂ) (s : ℂ) : ℂ :=
  (x : ℂ) ^ s * F s * mellinRampKernel s

def mellinVerticalSegment (x : ℝ) (F : ℂ → ℂ) (σ H : ℝ) : ℂ :=
  ∫ t : ℝ in -H..H, mellinContourIntegrand x F ((σ : ℂ) + t * I)

def mellinHorizontalSegment (x : ℝ) (F : ℂ → ℂ) (t a b : ℝ) : ℂ :=
  ∫ σ : ℝ in a..b, mellinContourIntegrand x F ((σ : ℂ) + t * I)

theorem differentiableOn_mellinContourIntegrand (x : ℝ) (hx : 0 < x)
    (F : ℂ → ℂ) (a b H : ℝ) (ha : 0 < a)
    (hF : DifferentiableOn ℂ F (Icc a b ×ℂ Icc (-H) H)) :
    DifferentiableOn ℂ (mellinContourIntegrand x F) (Icc a b ×ℂ Icc (-H) H) := by
  have hs0 (s : ℂ) (hs : s ∈ Icc a b ×ℂ Icc (-H) H) : s ≠ 0 := by
    have hsr : a ≤ s.re := hs.1.1
    intro h
    simp only [h, zero_re] at hsr
    linarith
  have hs1 (s : ℂ) (hs : s ∈ Icc a b ×ℂ Icc (-H) H) : s + 1 ≠ 0 := by
    have hsr : a ≤ s.re := hs.1.1
    intro h
    have hh := congrArg Complex.re h
    simp only [add_re, one_re, zero_re] at hh
    linarith
  have hK : DifferentiableOn ℂ mellinRampKernel (Icc a b ×ℂ Icc (-H) H) := by
    unfold mellinRampKernel
    exact (differentiableOn_const 1).div
      (differentiableOn_id.mul (differentiableOn_id.add_const 1))
      (fun s hs => mul_ne_zero (hs0 s hs) (hs1 s hs))
  exact ((differentiableOn_id.const_cpow
    (.inl (Complex.ofReal_ne_zero.mpr hx.ne'))).mul hF).mul hK

/-- Exact orientation of the upward vertical integrals in the rectangle.-/
theorem mellinVerticalSegment_sub_eq (x : ℝ) (hx : 0 < x) (F : ℂ → ℂ)
    (a b H : ℝ) (ha : 0 < a) (hab : a ≤ b) (hH : 0 ≤ H)
    (hF : DifferentiableOn ℂ F (Icc a b ×ℂ Icc (-H) H)) :
    mellinVerticalSegment x F b H - mellinVerticalSegment x F a H =
      I * (mellinHorizontalSegment x F (-H) a b - mellinHorizontalSegment x F H a b) := by
  have hd := differentiableOn_mellinContourIntegrand x hx F a b H ha hF
  have hC := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (mellinContourIntegrand x F) ((a : ℂ) + (-H) * I) ((b : ℂ) + H * I)
    (by simpa only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero, add_im, mul_im, zero_add, mul_one,
      neg_re, neg_im, neg_zero,
      uIcc_of_le hab, uIcc_of_le (show -H ≤ H by linarith)] using hd)
  have hC' : mellinHorizontalSegment x F (-H) a b - mellinHorizontalSegment x F H a b +
      I * mellinVerticalSegment x F b H - I * mellinVerticalSegment x F a H = 0 := by
    simpa only [mellinHorizontalSegment, mellinVerticalSegment,
      add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero,
      add_zero, add_im, mul_im, zero_add, mul_one, neg_re, neg_im, neg_zero,
      smul_eq_mul, ofReal_neg] using hC
  have heq : I * (mellinVerticalSegment x F b H - mellinVerticalSegment x F a H) =
      -(mellinHorizontalSegment x F (-H) a b - mellinHorizontalSegment x F H a b) := by
    linear_combination hC'
  calc
    _ = (-I) * (I * (mellinVerticalSegment x F b H - mellinVerticalSegment x F a H)) := by
      rw [← mul_assoc, neg_mul, I_mul_I, neg_neg, one_mul]
    _ = (-I) * (-(mellinHorizontalSegment x F (-H) a b -
        mellinHorizontalSegment x F H a b)) := congrArg (fun z : ℂ => (-I) * z) heq
    _ = _ := by ring

theorem norm_mellinRampKernel_le_one_div_im_sq (s : ℂ) (hs : s.im ≠ 0) :
    ‖mellinRampKernel s‖ ≤ 1 / s.im ^ 2 := by
  have h0 := Complex.abs_im_le_norm s
  have h1 : |s.im| ≤ ‖s + 1‖ := by simpa using Complex.abs_im_le_norm (s + 1)
  have hprod : s.im ^ 2 ≤ ‖s‖ * ‖s + 1‖ := by
    calc
      _ = |s.im| * |s.im| := by rw [← pow_two, sq_abs]
      _ ≤ _ := mul_le_mul h0 h1 (abs_nonneg _) (norm_nonneg s)
  rw [mellinRampKernel, norm_div, norm_one, norm_mul]
  exact one_div_le_one_div_of_le (sq_pos_of_ne_zero hs) hprod

theorem norm_mellinContourIntegrand_horizontal_le (x : ℝ) (hx : 1 ≤ x)
    (F : ℂ → ℂ) (b M σ t : ℝ) (hM : 0 ≤ M) (hσ : σ ≤ b) (ht : t ≠ 0)
    (hF : ‖F ((σ : ℂ) + t * I)‖ ≤ M) :
    ‖mellinContourIntegrand x F ((σ : ℂ) + t * I)‖ ≤ x ^ b * M / t ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hpow : ‖(x : ℂ) ^ ((σ : ℂ) + t * I)‖ ≤ x ^ b := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero]
    exact Real.rpow_le_rpow_of_exponent_le hx hσ
  have hK : ‖mellinRampKernel ((σ : ℂ) + t * I)‖ ≤ 1 / t ^ 2 := by
    simpa using norm_mellinRampKernel_le_one_div_im_sq ((σ : ℂ) + t * I) (by simpa using ht)
  rw [mellinContourIntegrand, norm_mul, norm_mul]
  have hprod := mul_le_mul hpow hF (norm_nonneg _) (Real.rpow_nonneg (by linarith) _)
  have hfinal := mul_le_mul hprod hK (norm_nonneg _)
    (mul_nonneg (Real.rpow_nonneg (by linarith) _) hM)
  simpa only [mul_one_div] using hfinal

theorem norm_mellinHorizontalSegment_le (x : ℝ) (hx : 1 ≤ x) (F : ℂ → ℂ)
    (a b t M : ℝ) (hab : a ≤ b) (ht : t ≠ 0) (hM : 0 ≤ M)
    (hF : ∀ σ ∈ Icc a b, ‖F ((σ : ℂ) + t * I)‖ ≤ M) :
    ‖mellinHorizontalSegment x F t a b‖ ≤ (b - a) * x ^ b * M / t ^ 2 := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := x ^ b * M / t ^ 2)
    (f := fun σ : ℝ => mellinContourIntegrand x F ((σ : ℂ) + t * I))
    (fun σ hσ => norm_mellinContourIntegrand_horizontal_le x hx F b M σ t hM
      (show σ ≤ b from (uIoc_of_le hab ▸ hσ).2) ht
      (hF σ ⟨(uIoc_of_le hab ▸ hσ).1.le, (uIoc_of_le hab ▸ hσ).2⟩))
  change ‖mellinHorizontalSegment x F t a b‖ ≤ _ at hb
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hb
  convert hb using 1; ring

theorem norm_mellinHorizontalDifference_le (x : ℝ) (hx : 1 ≤ x) (F : ℂ → ℂ)
    (a b H M : ℝ) (hab : a ≤ b) (hH : 0 < H) (hM : 0 ≤ M)
    (hF : ∀ s ∈ Icc a b ×ℂ Icc (-H) H, ‖F s‖ ≤ M) :
    ‖mellinHorizontalSegment x F (-H) a b - mellinHorizontalSegment x F H a b‖ ≤
      2 * (b - a) * x ^ b * M / H ^ 2 := by
  have hbottom := norm_mellinHorizontalSegment_le x hx F a b (-H) M hab (neg_ne_zero.mpr hH.ne') hM
    (fun σ hσ => hF _ (by
      change ((σ : ℂ) + ((-H : ℝ) : ℂ) * I).re ∈ Icc a b ∧
        ((σ : ℂ) + ((-H : ℝ) : ℂ) * I).im ∈ Icc (-H) H
      simpa using And.intro hσ (show -H ∈ Icc (-H) H by constructor <;> linarith)))
  have htop := norm_mellinHorizontalSegment_le x hx F a b H M hab hH.ne' hM
    (fun σ hσ => hF _ (by
      change ((σ : ℂ) + (H : ℂ) * I).re ∈ Icc a b ∧
        ((σ : ℂ) + (H : ℂ) * I).im ∈ Icc (-H) H
      simpa using And.intro hσ (show H ∈ Icc (-H) H by constructor <;> linarith)))
  have hn := (norm_sub_le (mellinHorizontalSegment x F (-H) a b)
    (mellinHorizontalSegment x F H a b)).trans (add_le_add hbottom htop)
  simpa only [neg_sq, ← two_mul, mul_div_assoc, mul_assoc] using hn

/-- An integrable kernel majorant gives a vertical bound independent of height.-/
theorem norm_mellinVerticalSegment_le (x : ℝ) (hx : 0 < x) (F : ℂ → ℂ)
    (a H M : ℝ) (ha : 0 < a) (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hF : ∀ t ∈ Icc (-H) H, ‖F ((a : ℂ) + t * I)‖ ≤ M) :
    ‖mellinVerticalSegment x F a H‖ ≤ Real.pi * (1 + (a ^ 2)⁻¹) * x ^ a * M := by
  let C : ℝ := x ^ a * M * (1 + (a ^ 2)⁻¹)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpoint (t : ℝ) (ht : t ∈ Ioc (-H) H) :
      ‖mellinContourIntegrand x F ((a : ℂ) + t * I)‖ ≤ C * (1 + t ^ 2)⁻¹ := by
    have hpow : ‖(x : ℂ) ^ ((a : ℂ) + t * I)‖ = x ^ a := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp
    rw [mellinContourIntegrand, norm_mul, norm_mul, hpow]
    have hprod := mul_le_mul_of_nonneg_left (hF t ⟨ht.1.le, ht.2⟩) (Real.rpow_nonneg hx.le a)
    have hfinal := mul_le_mul hprod (norm_mellinRampKernel_vertical_le a ha t) (norm_nonneg _)
      (mul_nonneg (Real.rpow_nonneg hx.le a) hM)
    simpa only [C, mul_assoc] using hfinal
  have hint : IntervalIntegrable (fun t : ℝ => C * (1 + t ^ 2)⁻¹) volume (-H) H :=
    ((integrable_inv_one_add_sq.const_mul C).intervalIntegrable)
  have hbound := intervalIntegral.norm_integral_le_of_norm_le (show -H ≤ H by linarith)
    (Filter.Eventually.of_forall hpoint) hint
  rw [intervalIntegral.integral_const_mul, integral_inv_one_add_sq] at hbound
  have harctan : Real.arctan H - Real.arctan (-H) ≤ Real.pi := by
    linarith [Real.arctan_lt_pi_div_two H, Real.neg_pi_div_two_lt_arctan (-H)]
  apply hbound.trans
  have hb := mul_le_mul_of_nonneg_left harctan hC
  simpa only [C, mul_comm, mul_left_comm, mul_assoc] using hb

/-- A finite contour estimate, with the horizontal contribution displayed.-/
theorem norm_mellinVerticalSegment_right_le (x : ℝ) (hx : 1 ≤ x) (F : ℂ → ℂ)
    (a b H M : ℝ) (ha : 0 < a) (hab : a ≤ b) (hH : 0 < H) (hM : 0 ≤ M)
    (hd : DifferentiableOn ℂ F (Icc a b ×ℂ Icc (-H) H))
    (hF : ∀ s ∈ Icc a b ×ℂ Icc (-H) H, ‖F s‖ ≤ M) :
    ‖mellinVerticalSegment x F b H‖ ≤
      Real.pi * (1 + (a ^ 2)⁻¹) * x ^ a * M +
        2 * (b - a) * x ^ b * M / H ^ 2 := by
  have heq := mellinVerticalSegment_sub_eq x (by linarith) F a b H ha hab hH.le hd
  have hleft := norm_mellinVerticalSegment_le x (by linarith) F a H M ha hH.le hM
    (fun t ht => hF _ (by
      change ((a : ℂ) + (t : ℂ) * I).re ∈ Icc a b ∧
        ((a : ℂ) + (t : ℂ) * I).im ∈ Icc (-H) H
      simpa using And.intro (show a ∈ Icc a b from ⟨le_rfl, hab⟩) ht))
  have hhorizontal := norm_mellinHorizontalDifference_le x hx F a b H M hab hH hM hF
  have hsplit : mellinVerticalSegment x F b H = mellinVerticalSegment x F a H +
      I * (mellinHorizontalSegment x F (-H) a b - mellinHorizontalSegment x F H a b) := by
    linear_combination heq
  rw [hsplit]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_I, one_mul]
  exact add_le_add hleft hhorizontal

end TwinPrime.Analytic
