import Tengoku.Piirrationalitymeasure.Formalization.IntegralDecomposition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Rational evaluation of every nonlogarithmic pole integral before denominator clearing. -/

namespace PiIrrationality

def giThreeAddI : GI := ⟨3, 1⟩

/--
@isnad1 id=eq.0h0v.s5.3776fd4272d0 from=translated src=- shape=62d93820 vocab=46c0e1b7
-/
theorem giThreeAddI_cast : (giThreeAddI : ℂ) = 3 + Complex.I := by
  simp [giThreeAddI, GaussianInt.toComplex_def']

/--
@isnad1 id=eq.0h2v.s7.a5f0d7572ce4 from=translated src=- shape=161c0d10 vocab=697fc361
-/
theorem gaussian_power_sub_conj (z : GI) (j : ℕ) :
    (z : ℂ) ^ j - (star (z : ℂ)) ^ j = 2 * (((z ^ j).im : ℤ) : ℂ) * Complex.I := by
  have h (w : GI) : (w : ℂ) - star (w : ℂ) = 2 * ((w.im : ℤ) : ℂ) * Complex.I := by
    rw [GaussianInt.toComplex_def]
    simp only [map_add, map_mul, Complex.star_def, map_intCast, Complex.conj_I]
    ring
  simpa only [map_pow, star_pow] using h (z ^ j)

noncomputable def poleIntegralRat (j : ℕ) : ℚ :=
  -2 / (j : ℚ) * (((giTwoAddI ^ j).im : ℚ) / 10 ^ j + ((giThreeAddI ^ j).im : ℚ) / 20 ^ j)

/--
@isnad1 id=eq.1h1v.s5.6cd0c539371c from=translated src=- shape=6702122b vocab=d76e1426
-/
theorem polePair_integral_rat (j : ℕ) (hj : 0 < j) :
    -(∫ s : ℝ in (-2)..2, polePair j s) = (poleIntegralRat j : ℂ) := by
  have h1 : (4 - 2 * Complex.I)⁻¹ = (giTwoAddI : ℂ) / 10 := by
    rw [giTwoAddI_toComplex]
    apply Complex.ext <;> norm_num [Complex.inv_re, Complex.inv_im,
      Complex.div_re, Complex.div_im, Complex.normSq]
  have h2 : (4 + 2 * Complex.I)⁻¹ = star (giTwoAddI : ℂ) / 10 := by
    rw [giTwoAddI_toComplex]
    apply Complex.ext <;> norm_num [Complex.inv_re, Complex.inv_im,
      Complex.div_re, Complex.div_im, Complex.normSq]
  have h3 : (6 + 2 * Complex.I)⁻¹ = star (giThreeAddI : ℂ) / 20 := by
    rw [giThreeAddI_cast]
    apply Complex.ext <;> norm_num [Complex.inv_re, Complex.inv_im,
      Complex.div_re, Complex.div_im, Complex.normSq]
  have h4 : (6 - 2 * Complex.I)⁻¹ = (giThreeAddI : ℂ) / 20 := by
    rw [giThreeAddI_cast]
    apply Complex.ext <;> norm_num [Complex.inv_re, Complex.inv_im,
      Complex.div_re, Complex.div_im, Complex.normSq]
  rw [polePair_integral j hj]
  simp only [zpow_neg, zpow_natCast, ← inv_pow, h1, h2, h3, h4, div_pow]
  have he : (giTwoAddI : ℂ) ^ j / 10 ^ j - (star (giTwoAddI : ℂ)) ^ j / 10 ^ j -
      (star (giThreeAddI : ℂ)) ^ j / 20 ^ j + (giThreeAddI : ℂ) ^ j / 20 ^ j =
        ((giTwoAddI : ℂ) ^ j - (star (giTwoAddI : ℂ)) ^ j) / 10 ^ j +
        ((giThreeAddI : ℂ) ^ j - (star (giThreeAddI : ℂ)) ^ j) / 20 ^ j := by ring
  rw [he, gaussian_power_sub_conj, gaussian_power_sub_conj]
  unfold poleIntegralRat
  push_cast
  ring_nf
  simp [Complex.I_sq]
  ring

/--
@isnad1 id=eq.0h2v.s6.149053e3fa1c from=translated src=- shape=2861bd0f vocab=61deb593
-/
theorem rational_nonlog_pole_integral (m : ℕ) (a : ℕ → ℚ) :
    -(∫ s : ℝ in (-2)..2, ∑ j ∈ Finset.Icc 1 m, (a j : ℂ) * polePair j s) =
      ((∑ j ∈ Finset.Icc 1 m, a j * poleIntegralRat j : ℚ) : ℂ) := by
  rw [intervalIntegral.integral_finsetSum]
  · rw [← Finset.sum_neg_distrib]
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    rw [intervalIntegral.integral_const_mul, neg_mul_eq_mul_neg,
      polePair_integral_rat j (by have h := (Finset.mem_Icc.mp hj).1; omega)]
  · intro j hj
    exact (continuous_const.mul (polePair_continuous j)).intervalIntegrable _ _

end PiIrrationality
