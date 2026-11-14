import Tengoku.Piirrationalitymeasure.Formalization.SavingPeriodDifference

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Saving-integral convergence without a sign restriction on a + 2*b - c. -/

namespace PiIrrationality

open MeasureTheory Set

theorem savingDensity_initial_zero_nonneg {A B C K t : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hAK : A ≤ K) (hBK : B ≤ K) (hCK : C ≤ K)
    (ht0 : 0 < t) (ht1 : t ≤ 1 / (4 * (K + 1))) : savingDensity A B C t = 0 := by
  have hmul := (le_div_iff₀ (show 0 < 4 * (K + 1) by positivity)).mp ht1
  have hKt : K * t < 1 / 4 := by nlinarith
  have hAt := mul_le_mul_of_nonneg_right hAK ht0.le
  have hBt := mul_le_mul_of_nonneg_right hBK ht0.le
  have hCt := mul_le_mul_of_nonneg_right hCK ht0.le
  have hAp := mul_nonneg hA ht0.le
  have hBp := mul_nonneg hB ht0.le
  have hCp := mul_nonneg hC ht0.le
  unfold savingDensity savingChi
  rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩,
    Int.fract_eq_self.mpr ⟨hBp, by linarith⟩,
    Int.fract_eq_self.mpr ⟨hCp, by linarith⟩, ite_eq_right (by linarith), zero_div]

theorem savingDensity_integrableOn_nonneg {A B C : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    IntegrableOn (savingDensity A B C) (Ioi (0 : ℝ)) := by
  let K := A + B + C
  let delta := 1 / (4 * (K + 1))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hd : 0 < delta := by dsimp [delta]; positivity
  have hz : ∀ t ∈ Ioc (0 : ℝ) delta, savingDensity A B C t = 0 := by
    intro t ht
    exact savingDensity_initial_zero_nonneg hA hB hC hK
      (by dsimp [K]; linarith) (by dsimp [K]; linarith) (by dsimp [K]; linarith)
      ht.1 ht.2
  have hfirst : IntegrableOn (savingDensity A B C) (Ioc (0 : ℝ) delta) := by
    have hzero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioc (0 : ℝ) delta) volume :=
      integrableOn_zero
    exact hzero.congr_fun (fun t ht => (hz t ht).symm) measurableSet_Ioc
  have hpower : IntegrableOn (fun t : ℝ => 1 / t ^ 2) (Ioi delta) := by
    apply (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hd).congr_fun
      _ measurableSet_Ioi
    intro t ht
    dsimp only
    rw [Real.rpow_neg (hd.trans ht).le, Real.rpow_two, one_div]
  have htail : IntegrableOn (savingDensity A B C) (Ioi delta) := by
    apply hpower.mono' (measurable_savingDensity A B C).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (savingDensity_nonneg A B C t)]
    exact div_le_div_of_nonneg_right (savingChi_le_one _ _ _) (sq_nonneg t)
  have hu : Ioc (0 : ℝ) delta ∪ Ioi delta = Ioi (0 : ℝ) := by
    ext t
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (⟨ht, _⟩ | ht) <;> linarith
    · intro ht
      by_cases htd : t ≤ delta
      · exact Or.inl ⟨ht, htd⟩
      · exact Or.inr (lt_of_not_ge htd)
  rw [← hu]
  exact hfirst.union htail

theorem savingOmega_difference_hasSum_nonneg (a b c : ℤ) (h : ℝ × ℝ)
    (ha : 0 ≤ (a : ℝ)) (hb : 0 ≤ (b : ℝ)) (hc : 0 ≤ (c : ℝ))
    (hah : 0 ≤ (a : ℝ) + h.1) (hbh : 0 ≤ (b : ℝ) + h.2) :
    HasSum (fun k : ℕ => savingPeriodDifference a b c h k)
      (savingOmega ((a : ℝ) + h.1) ((b : ℝ) + h.2) c - savingOmega a b c) := by
  have hi := savingDensity_integrableOn_nonneg hah hbh hc
  have hj := savingDensity_integrableOn_nonneg ha hb hc
  have hs := hasSum_integral_shifted_periods (hi.sub hj)
  simp only [Pi.sub_apply] at hs
  rw [integral_sub hi hj] at hs
  convert hs using 1
  · funext k
    unfold savingPeriodDifference
    apply intervalIntegral.integral_congr
    intro u _
    exact (savingDensity_shifted_difference a b c h k u).symm
  · rfl

end PiIrrationality
