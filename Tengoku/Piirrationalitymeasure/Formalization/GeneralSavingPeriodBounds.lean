import Tengoku.Piirrationalitymeasure.Formalization.GeneralSavingIntegrability
import Tengoku.Piirrationalitymeasure.Formalization.SavingPeriodTail

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Uniform first-period and tail estimates for arbitrary positive integer parameters. -/

namespace PiIrrationality

open MeasureTheory Set

noncomputable def savingPerturbationRadius (a b : ℝ) : ℝ :=
  min 1 (min (a / 2) (b / 2))

/--
@isnad1 id=lt.2h2v.s5.3aacf2a6bf9d from=translated src=- shape=6c67d60b vocab=7d62e24e
-/
theorem savingPerturbationRadius_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < savingPerturbationRadius a b := by
  unfold savingPerturbationRadius
  positivity

/--
@isnad1 id=le.0h2v.s4.1b88bb7c785e from=translated src=- shape=aa052b1b vocab=aff2ce1f
-/
theorem savingPerturbationRadius_le_one (a b : ℝ) : savingPerturbationRadius a b ≤ 1 :=
  min_le_left _ _

/--
@isnad1 id=and.4h4v.s7.9164a06dcb72 from=translated src=- shape=dd457aa3 vocab=5c5232b6
-/
theorem savingPerturbation_bounds {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c)
    {h : ℝ × ℝ} (hh : parameterNormOne h ≤ savingPerturbationRadius a b) :
    0 ≤ a + h.1 ∧ 0 ≤ b + h.2 ∧
      a + h.1 ≤ a + b + c + 1 ∧ b + h.2 ≤ a + b + c + 1 := by
  have h1 : parameterNormOne h ≤ 1 := hh.trans (savingPerturbationRadius_le_one a b)
  have hA : parameterNormOne h ≤ a / 2 :=
    hh.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hB : parameterNormOne h ≤ b / 2 :=
    hh.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hx : |h.1| ≤ parameterNormOne h := by
    dsimp [parameterNormOne]
    linarith [abs_nonneg h.2]
  have hy : |h.2| ≤ parameterNormOne h := by
    dsimp [parameterNormOne]
    linarith [abs_nonneg h.1]
  have hx0 := neg_abs_le h.1
  have hx1 := le_abs_self h.1
  have hy0 := neg_abs_le h.2
  have hy1 := le_abs_self h.2
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/--
@isnad1 id=le.5h4v.s7.2f41351fcb5b from=translated src=- shape=59ecdb48 vocab=41e458ee
-/
theorem savingPeriodDifference_zero_bound_general {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) (hq : a + 2 * b - c ≠ 0)
    {h : ℝ × ℝ} (hh : parameterNormOne h ≤ savingPerturbationRadius a b) :
    |savingPeriodDifference a b c h 0| ≤
      (4 * (a + b + c + 2)) ^ 2 * savingTranslationConstant a b c * parameterNormOne h := by
  obtain ⟨hah, hbh, haK, hbK⟩ := savingPerturbation_bounds ha hb hc hh
  let K := a + b + c + 1
  let B := 4 * (a + b + c + 2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  let f : ℝ → ℝ := fun t => savingDensity (a + h.1) (b + h.2) c t - savingDensity a b c t
  let g : ℝ → ℝ := fun t => translatedSavingChi a b c (t • h) t - translatedSavingChi a b c 0 t
  have hfg (t : ℝ) : f t = g t / t ^ 2 := by
    dsimp [f, g, savingDensity, translatedSavingChi]
    congr 1
    rw [← sub_div]
    congr 2 <;> ring
  have hz {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / B)) : f t = 0 := by
    rcases ht.1.eq_or_lt with ht0 | ht0
    · simp [← ht0, f, savingDensity]
    have he : t ≤ 1 / (4 * (K + 1)) := by
      simpa only [B, K, add_assoc, show (1 : ℝ) + 1 = 2 by norm_num] using ht.2
    dsimp [f]
    rw [savingDensity_initial_zero_nonneg hah hbh hc hK haK hbK
        (by dsimp [K]; linarith) ht0 he,
      savingDensity_initial_zero_nonneg ha.le hb.le hc hK
        (by dsimp [K]; linarith) (by dsimp [K]; linarith)
        (by dsimp [K]; linarith) ht0 he, sub_self]
  have hi : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      (((savingDensity_integrableOn_nonneg hah hbh hc).sub
        (savingDensity_integrableOn_nonneg ha.le hb.le hc)).mono_set (fun _ ht => ht.1))
  have hj : IntervalIntegrable g volume 0 1 := by
    simpa only [g, zero_add] using
      (translatedSavingChi_affine_intervalIntegrable a b c 0 h).sub
        (translatedSavingChi_intervalIntegrable a b c 0)
  have hp : ∀ t ∈ Icc (0 : ℝ) 1, |f t| ≤ B ^ 2 * |g t| := by
    intro t ht
    by_cases hsmall : t ≤ 1 / B
    · rw [hz ⟨ht.1, hsmall⟩]
      simp only [abs_zero]
      positivity
    · have ht0 : 0 < t := lt_of_lt_of_le (by positivity : 0 < 1 / B) (le_of_not_ge hsmall)
      have hsq : 1 / t ^ 2 ≤ B ^ 2 := by
        have hs : (1 / B) ^ 2 ≤ t ^ 2 := by nlinarith [one_div_pos.mpr hB]
        have hbound := one_div_le_one_div_of_le (sq_pos_of_pos (one_div_pos.mpr hB)) hs
        simpa only [one_div, inv_pow, inv_inv] using hbound
      rw [hfg, abs_div, abs_of_pos (sq_pos_of_pos ht0), div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right hsq (abs_nonneg _)
  have hg : (∫ t in (0 : ℝ)..1, |g t|) ≤
      savingTranslationConstant a b c * parameterNormOne h := by
    simpa only [g, zero_add] using
      translatedSavingChi_integral_affine_translation 0 h ha.ne' hb.ne' hq
        (by norm_num [parameterNormOne]) (hh.trans (savingPerturbationRadius_le_one a b))
  have he : savingPeriodDifference a b c h 0 = ∫ t in (0 : ℝ)..1, f t := by
    unfold savingPeriodDifference
    simp only [zero_add]
    apply intervalIntegral.integral_congr
    intro t _
    exact (hfg t).symm
  rw [he]
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, |f t| := intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ t in (0 : ℝ)..1, B ^ 2 * |g t| :=
      intervalIntegral.integral_mono_on (by norm_num) hi.abs (hj.abs.const_mul _) hp
    _ = B ^ 2 * ∫ t in (0 : ℝ)..1, |g t| := intervalIntegral.integral_const_mul _ _
    _ ≤ B ^ 2 * (savingTranslationConstant a b c * parameterNormOne h) := by gcongr
    _ = _ := by dsimp [B]; ring

/--
@isnad1 id=le.4h5v.s7.3a5e6149dec8 from=translated src=- shape=d53da082 vocab=3290ba94
-/
theorem savingOmega_period_remainder_general (a b c : ℤ)
    (ha : 0 < (a : ℝ)) (hb : 0 < (b : ℝ)) (hc : 0 ≤ (c : ℝ))
    {h : ℝ × ℝ} (hh : parameterNormOne h ≤ savingPerturbationRadius a b) (K : ℕ) :
    |savingOmega ((a : ℝ) + h.1) ((b : ℝ) + h.2) c - savingOmega a b c -
        savingPeriodDifference a b c h 0 -
        ∑ k ∈ Finset.Icc 1 K, savingPeriodDifference a b c h k| ≤ 2 / ((K : ℝ) + 1) := by
  obtain ⟨hah, hbh, _, _⟩ := savingPerturbation_bounds ha hb hc hh
  have hs := savingOmega_difference_hasSum_nonneg a b c h ha.le hb.le hc hah hbh
  have ht := hasSum_inverse_square_tail hs (fun k hk =>
    savingPeriodDifference_abs_le a b c h (by exact_mod_cast hk)) (N := K + 1) (by omega)
  have he (f : ℕ → ℝ) : (∑ k ∈ Finset.range (K + 1), f k) =
      f 0 + ∑ k ∈ Finset.Icc 1 K, f k := by
    have hsum := Finset.sum_Ico_eq_sub (f := f) (by omega : 1 ≤ K + 1)
    simp only [Finset.sum_range_one, Finset.Ico_add_one_right_eq_Icc] at hsum
    linarith
  rw [he] at ht
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_add_eq_sub_sub] using ht

end PiIrrationality
