import Tengoku.Piirrationalitymeasure.Formalization.PoleIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The logarithmic integral (2.3), evaluated along the vertical segment.
A real arctangent/logarithm primitive also fixes the branch unambiguously.
-/

namespace PiIrrationality

noncomputable def logarithmicPrimitive (s : ℝ) : ℂ :=
  ((Real.arctan (s / 4) + Real.arctan (s / 6) : ℝ) : ℂ) +
    Complex.I / 2 * ((Real.log (s ^ 2 + 36) - Real.log (s ^ 2 + 16) : ℝ) : ℂ)

theorem logarithmicPrimitive_hasDerivAt (s : ℝ) :
    HasDerivAt logarithmicPrimitive (polePair 0 s) s := by
  have h16 : s ^ 2 + 16 ≠ 0 := by positivity
  have h36 : s ^ 2 + 36 ≠ 0 := by positivity
  have h16' : 16 + s ^ 2 ≠ 0 := by positivity
  have h36' : 36 + s ^ 2 ≠ 0 := by positivity
  have h4den : 1 + (s / 4) ^ 2 ≠ 0 := by positivity
  have h6den : 1 + (s / 6) ^ 2 ≠ 0 := by positivity
  have h4 := (Real.hasDerivAt_arctan (s / 4)).comp s ((hasDerivAt_id s).div_const 4)
  have h6 := (Real.hasDerivAt_arctan (s / 6)).comp s ((hasDerivAt_id s).div_const 6)
  have hl16 := (Real.hasDerivAt_log h16).comp s ((hasDerivAt_pow 2 s).add_const 16)
  have hl36 := (Real.hasDerivAt_log h36).comp s ((hasDerivAt_pow 2 s).add_const 36)
  have hd := (h4.add h6).ofReal_comp.add
    ((hl36.sub hl16).ofReal_comp.const_mul (Complex.I / 2))
  convert hd using 1 <;> try rfl
  apply Complex.ext <;>
    norm_num only [polePair, zpow_neg_one, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.inv_re, Complex.inv_im, Complex.div_re, Complex.div_im,
      Complex.normSq_apply, Complex.natCast_re, Complex.natCast_im,
      Complex.re_ofNat, Complex.im_ofNat]
  all_goals ring_nf
  all_goals field_simp [h16', h36', h16, h36, h4den, h6den]
  all_goals ring

theorem arctan_half_add_third :
    Real.arctan (1 / 2) + Real.arctan (1 / 3) = Real.pi / 4 := by
  rw [Real.arctan_add (by norm_num : (1 / 2 : ℝ) * (1 / 3) < 1)]
  norm_num [Real.arctan_one]

theorem logarithmicPrimitive_endpoint_difference :
    logarithmicPrimitive 2 - logarithmicPrimitive (-2) = (Real.pi : ℂ) / 2 := by
  unfold logarithmicPrimitive
  norm_num only [neg_sq, Nat.reducePow, neg_div, Real.arctan_neg]
  simp only [Complex.ofReal_add, Complex.ofReal_neg, Complex.ofReal_sub]
  have ha : (Real.arctan (1 / 2) : ℂ) + (Real.arctan (1 / 3) : ℂ) = (Real.pi : ℂ) / 4 := by
    exact_mod_cast arctan_half_add_third
  linear_combination 2 * ha

theorem logarithmicPole_integral :
    (∫ s : ℝ in (-2)..2, polePair 0 s) = (Real.pi : ℂ) / 2 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => logarithmicPrimitive_hasDerivAt s) ((polePair_continuous 0).intervalIntegrable _ _)]
  exact logarithmicPrimitive_endpoint_difference

theorem logarithmicPole_contour_integral :
    Complex.I * (∫ s : ℝ in (-2)..2, polePair 0 s) = (Real.pi : ℂ) * Complex.I / 2 := by
  rw [logarithmicPole_integral]
  ring

theorem logarithmicCoeff_integral (n : ℕ) :
    -(∫ s : ℝ in (-2)..2, (laurentCoeffRat n 0 : ℂ) * polePair 0 s) =
      (-laurentCoeffRat n 0 / 2 : ℚ) * (Real.pi : ℂ) := by
  rw [intervalIntegral.integral_const_mul, logarithmicPole_integral]
  push_cast
  ring

theorem normalizedLogarithmicIntegral_integerPi (n : ℕ) (hn : 1 ≤ n) :
    ∃ V : ℤ, (normalizationMultiplier n : ℂ) *
      (-(∫ s : ℝ in (-2)..2, (laurentCoeffRat n 0 : ℂ) * polePair 0 s)) =
        (V : ℂ) * (Real.pi : ℂ) := by
  obtain ⟨V, hV⟩ := normalizedPiCoeff_is_integer n hn
  refine ⟨V, ?_⟩
  have h : normalizationMultiplier n * (-laurentCoeffRat n 0 / 2) =
      normalizedPiCoeff n := by
    unfold normalizedPiCoeff
    ring
  rw [logarithmicCoeff_integral, ← mul_assoc, ← Rat.cast_mul, h, hV]
  push_cast
  rfl

end PiIrrationality
