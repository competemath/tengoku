import Tengoku.Piirrationalitymeasure.Formalization.SavingFirstPeriod
import Tengoku.Piirrationalitymeasure.Formalization.InverseSquareTail

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Uniform tails of the actual saving-integral period expansion. -/

namespace PiIrrationality

open MeasureTheory Set

/--
@isnad1 id=le.1h5v.s6.054aaeb93fb9 from=translated src=- shape=fe218592 vocab=e76e17dc
-/
theorem savingPeriodDifference_abs_le (a b c : ℝ) (h : ℝ × ℝ) {k : ℝ} (hk : 0 < k) :
    |savingPeriodDifference a b c h k| ≤ 1 / k ^ 2 := by
  let f : ℝ → ℝ := fun u => translatedSavingChi a b c ((k + u) • h) u -
    translatedSavingChi a b c 0 u
  have hi : IntervalIntegrable f volume 0 1 := by
    simpa only [f, add_smul] using
      (translatedSavingChi_affine_intervalIntegrable a b c (k • h) h).sub
        (translatedSavingChi_intervalIntegrable a b c 0)
  have hf : (∫ u in (0 : ℝ)..1, |f u|) ≤ 1 := by
    have hm : (∫ u in (0 : ℝ)..1, |f u|) ≤ ∫ _u in (0 : ℝ)..1, (1 : ℝ) := by
      apply intervalIntegral.integral_mono_on (by norm_num) hi.abs intervalIntegrable_const
      intro u _
      exact savingChi_abs_sub_le_one _ _ _ _ _ _
    simpa using hm
  have hw := intervalIntegral_abs_mul_le hi (continuousOn_inverse_square_shift hk)
    (C := 1 / k ^ 2) (fun u hu => by
      rw [abs_of_nonneg (by positivity : 0 ≤ 1 / (k + u) ^ 2)]
      exact inverse_square_shift_le hk hu.1)
  change |∫ u in (0 : ℝ)..1, f u / (k + u) ^ 2| ≤ _
  simpa only [div_eq_mul_inv, one_mul] using
    hw.trans (mul_le_of_le_one_left (by positivity) hf)

/--
@isnad1 id=le.1h2v.s7.10239207794d from=translated src=- shape=d85a12fa vocab=fa74d3e3
-/
theorem savingOmega_candidate_period_remainder {h : ℝ × ℝ} (hh : parameterNormOne h ≤ 1)
    (K : ℕ) :
    |savingOmega (1857 + h.1) (3714 + h.2) 5570 - savingOmega 1857 3714 5570 -
        savingPeriodDifference 1857 3714 5570 h 0 -
        ∑ k ∈ Finset.Icc 1 K, savingPeriodDifference 1857 3714 5570 h k| ≤
      2 / ((K : ℝ) + 1) := by
  obtain ⟨ha, hb, hq, _, _⟩ := savingCandidatePerturbation_bounds hh
  have hs := savingOmega_difference_hasSum 1857 3714 5570 h
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ha hb hq
  norm_num only [Int.cast_ofNat] at hs
  have ht := hasSum_inverse_square_tail hs (fun k hk =>
    savingPeriodDifference_abs_le 1857 3714 5570 h (by exact_mod_cast hk))
    (N := K + 1) (by omega)
  have he (f : ℕ → ℝ) : (∑ k ∈ Finset.range (K + 1), f k) =
      f 0 + ∑ k ∈ Finset.Icc 1 K, f k := by
    have hsum := Finset.sum_Ico_eq_sub (f := f) (by omega : 1 ≤ K + 1)
    simp only [Finset.sum_range_one, Finset.Ico_add_one_right_eq_Icc] at hsum
    linarith
  rw [he] at ht
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_add_eq_sub_sub] using ht

end PiIrrationality
