import Tengoku.Piirrationalitymeasure.Formalization.CoefficientConvergence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Strict maximal modulus at the positive point of each circle inside the unit disk. -/

namespace PiIrrationality

noncomputable def PComplex (z : ℂ) : ℂ :=
  2 + 6 * z + 9 * z ^ 2 + 6 * z ^ 3 + 2 * z ^ 4

noncomputable def SComplex (z : ℂ) : ℂ :=
  (1 + z) ^ 3714 * PComplex z ^ 3714 / (1 - z) ^ 7430

/--
@isnad1 id=hassum.1h1v.s7.d8edbdd88818 from=translated src=- shape=94868c31 vocab=993d6ee7
-/
theorem SComplex_hasSum {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k => (↑(PowerSeries.coeff k Sseries) : ℂ) * z ^ k) (SComplex z) :=
  Sseries_hasSum hz

/--
@isnad1 id=eq.0h1v.s3.acc0211077d7 from=translated src=- shape=c14c2a45 vocab=9e894c53
-/
theorem SComplex_ofReal (x : ℝ) : SComplex (x : ℂ) = (SReal x : ℂ) := by
  unfold SComplex PComplex SReal PReal
  push_cast
  rfl

/--
@isnad1 id=le.0h1v.s3.149c242d260a from=translated src=- shape=a5850310 vocab=a83ae0c3
-/
theorem PComplex_norm_le (z : ℂ) : ‖PComplex z‖ ≤ PReal ‖z‖ := by
  unfold PComplex PReal
  calc
    ‖2 + 6 * z + 9 * z ^ 2 + 6 * z ^ 3 + 2 * z ^ 4‖ ≤
        ‖(2 : ℂ)‖ + ‖6 * z‖ + ‖9 * z ^ 2‖ + ‖6 * z ^ 3‖ + ‖2 * z ^ 4‖ := by
      have h1 := norm_add_le (2 : ℂ) (6 * z)
      have h2 := norm_add_le (2 + 6 * z) (9 * z ^ 2)
      have h3 := norm_add_le (2 + 6 * z + 9 * z ^ 2) (6 * z ^ 3)
      have h4 := norm_add_le (2 + 6 * z + 9 * z ^ 2 + 6 * z ^ 3) (2 * z ^ 4)
      linarith
    _ = _ := by simp only [norm_mul, norm_pow]; norm_num

/--
@isnad1 id=lt.1h1v.s4.006d99fdabde from=translated src=- shape=82a34fa9 vocab=914d4d2d
-/
theorem complex_re_lt_norm {z : ℂ} (hz : z ≠ (‖z‖ : ℂ)) : z.re < ‖z‖ := by
  apply lt_of_le_of_ne (Complex.re_le_norm z)
  intro heq
  apply hz
  have him : z.im = 0 := by
    have hs := Complex.sq_norm z
    rw [Complex.normSq_apply, ← heq] at hs
    nlinarith [sq_nonneg z.im]
  exact Complex.ext (by simpa using heq) (by simpa using him)

/--
@isnad1 id=lt.2h1v.s5.9a0ea52d4c59 from=translated src=- shape=0cee96ac vocab=b730d4da
-/
theorem one_sub_complex_norm_strict {z : ℂ} (hz1 : ‖z‖ < 1)
    (hz : z ≠ (‖z‖ : ℂ)) : 1 - ‖z‖ < ‖1 - z‖ := by
  have hr := complex_re_lt_norm hz
  have hs := Complex.sq_norm (1 - z)
  have hzsq := Complex.sq_norm z
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re,
    Complex.sub_im, Complex.one_im] at hs hzsq
  nlinarith [norm_nonneg (1 - z), norm_nonneg z]

/--
@isnad1 id=ne.1h1v.s5.66695d3f34f3 from=translated src=- shape=e0aee735 vocab=0fcc4b44
-/
theorem one_sub_complex_ne_zero {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ≠ 0 := by
  intro h
  have h1 : z = 1 := by linear_combination -h
  simp [h1] at hz

/--
@isnad1 id=lt.2h1v.s5.7511484001c4 from=translated src=- shape=d29126cc vocab=992744b4
-/
theorem SComplex_norm_strict {z : ℂ} (hz1 : ‖z‖ < 1)
    (hz : z ≠ (‖z‖ : ℂ)) : ‖SComplex z‖ < SReal ‖z‖ := by
  have hplus : ‖1 + z‖ ≤ 1 + ‖z‖ := by simpa using norm_add_le (1 : ℂ) z
  have hden : 1 - ‖z‖ < ‖1 - z‖ := one_sub_complex_norm_strict hz1 hz
  have hdenpos : 0 < 1 - ‖z‖ := by linarith
  have hP := PReal_strictPositive ‖z‖ (norm_nonneg z)
  have hnum : 0 < (1 + ‖z‖) ^ 3714 * PReal ‖z‖ ^ 3714 := by positivity
  have hpow : (1 - ‖z‖) ^ 7430 < ‖1 - z‖ ^ 7430 := by
    exact pow_lt_pow_left₀ hden hdenpos.le (by norm_num)
  unfold SComplex SReal
  rw [norm_div, norm_mul, norm_pow, norm_pow, norm_pow]
  calc
    ‖1 + z‖ ^ 3714 * ‖PComplex z‖ ^ 3714 / ‖1 - z‖ ^ 7430 ≤
        (1 + ‖z‖) ^ 3714 * PReal ‖z‖ ^ 3714 / ‖1 - z‖ ^ 7430 := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg (norm_nonneg _) _)
      exact mul_le_mul
        (pow_le_pow_left₀ (norm_nonneg _) hplus 3714)
        (pow_le_pow_left₀ (norm_nonneg _) (PComplex_norm_le z) 3714)
        (pow_nonneg (norm_nonneg _) _) (by positivity)
    _ < _ := div_lt_div_of_pos_left hnum (pow_pos hdenpos _) hpow

/--
@isnad1 id=continuo.1h1v.s5.c569ae44dd71 from=translated src=- shape=1929e545 vocab=8db3c37a
-/
theorem SComplex_continuousAt {z : ℂ} (hz : ‖z‖ < 1) : ContinuousAt SComplex z := by
  unfold SComplex PComplex
  fun_prop (disch := exact pow_ne_zero _ (one_sub_complex_ne_zero hz))

/--
@isnad1 id=ex.5h2v.s7.a39ddc972da5 from=translated src=- shape=d8a89a9b vocab=fe498973
-/
theorem SComplex_compact_circle_bound {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {K : Set ℂ} (hK : IsCompact K) (hr : ∀ z ∈ K, ‖z‖ = r)
    (ha : ∀ z ∈ K, z ≠ (r : ℂ)) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ z ∈ K, ‖SComplex z‖ ≤ q * SReal r := by
  rcases K.eq_empty_or_nonempty with hE | hne
  · refine ⟨0, le_refl 0, by norm_num, ?_⟩
    simp [hE]
  have hc : ContinuousOn (fun z => ‖SComplex z‖) K := by
    intro z hz
    exact (SComplex_continuousAt (by rw [hr z hz]; exact hr1)).norm.continuousWithinAt
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hne hc
  have hS : 0 < SReal r := SReal_pos hr0 hr1
  have hstrict : ‖SComplex z‖ < SReal r := by
    have hzn : z ≠ (‖z‖ : ℂ) := by rw [hr z hz]; exact ha z hz
    simpa only [hr z hz] using SComplex_norm_strict (by rw [hr z hz]; exact hr1) hzn
  refine ⟨‖SComplex z‖ / SReal r, div_nonneg (norm_nonneg _) hS.le,
    (div_lt_one hS).mpr hstrict, ?_⟩
  intro w hw
  rw [div_mul_cancel₀ _ hS.ne']
  exact hmax hw

end PiIrrationality
