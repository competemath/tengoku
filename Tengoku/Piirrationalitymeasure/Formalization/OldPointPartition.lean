import Tengoku.Piirrationalitymeasure.Formalization.TranslatedSavingMeasure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The exact old-point partition, including the interval born at the period end. -/

namespace PiIrrationality

open MeasureTheory Set

noncomputable def oldPoint : ℝ × ℝ := (1 / 3, 2 / 3)

noncomputable def oldPointDifference (e u : ℝ) : ℝ :=
  Int.fract (u + e / 2 + 1 / 2) + 2 * Int.fract (2 * u + e) - Int.fract (3 * u)

/--
@isnad1 id=eq.3h2v.s9.0282cef1ab45 from=translated src=- shape=8d8e3289 vocab=cc74b5e3
-/
theorem oldPointDifference_formula {e u : ℝ} (he : 0 ≤ e) (he1 : e < 1 / 15)
    (hu : u ∈ Ico (0 : ℝ) 1) :
    oldPointDifference e u =
      if u < 1 / 3 then 2 * u + 1 / 2 + 5 * e / 2
      else if u < 1 / 2 - e / 2 then 2 * u + 3 / 2 + 5 * e / 2
      else if u < 2 / 3 then 2 * u - 3 / 2 + 5 * e / 2
      else if u < 1 - e / 2 then 2 * u - 1 / 2 + 5 * e / 2
      else 2 * u - 5 / 2 + 5 * e / 2 := by
  have hA : ⌊u + e / 2 + 1 / 2⌋ =
      if u < 1 / 2 - e / 2 then (0 : ℤ) else 1 := by
    split_ifs with h <;> apply Int.floor_eq_iff.mpr <;> constructor <;> norm_num <;> linarith [hu.1, hu.2]
  have hB : ⌊2 * u + e⌋ =
      if u < 1 / 2 - e / 2 then (0 : ℤ) else if u < 1 - e / 2 then 1 else 2 := by
    split_ifs <;> apply Int.floor_eq_iff.mpr <;> constructor <;> norm_num <;> linarith [hu.1, hu.2]
  have hC : ⌊3 * u⌋ = if u < 1 / 3 then (0 : ℤ) else if u < 2 / 3 then 1 else 2 := by
    split_ifs <;> apply Int.floor_eq_iff.mpr <;> constructor <;> norm_num <;> linarith [hu.1, hu.2]
  unfold oldPointDifference
  simp only [Int.fract, hA, hB, hC]
  split_ifs <;> push_cast <;> linarith [hu.1, hu.2]

/--
@isnad1 id=iff.3h2v.s7.8cbab0d04b2c from=translated src=- shape=c03d5151 vocab=ea11dc3f
-/
theorem oldPointDifference_neg_iff {e u : ℝ} (he : 0 ≤ e) (he1 : e < 1 / 15)
    (hu : u ∈ Ico (0 : ℝ) 1) :
    oldPointDifference e u < 0 ↔
      u ∈ Ico (1 / 2 - e / 2) (2 / 3) ∪ Ico (1 - e / 2) 1 := by
  rw [oldPointDifference_formula he he1 hu]
  simp only [mem_union, mem_Ico]
  split_ifs <;> constructor <;> intro h
  all_goals first
    | exact Or.inl ⟨by linarith, by linarith⟩
    | exact Or.inr ⟨by linarith, hu.2⟩
    | linarith [hu.1, hu.2]
    | rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith [hu.1, hu.2]

/--
@isnad1 id=eq.2h1v.s7.d0eee5df00a7 from=translated src=- shape=03c16932 vocab=5c84d9e9
-/
theorem oldPoint_accepted_set {e : ℝ} (he : 0 ≤ e) (he1 : e < 1 / 15) :
    {u : ℝ | u ∈ Ico (0 : ℝ) 1 ∧ translatedSavingChi 1 2 3 (e / 2, e) u = 1} =
      Ico (1 / 2 - e / 2) (2 / 3) ∪ Ico (1 - e / 2) 1 := by
  ext u
  have hchi : translatedSavingChi 1 2 3 (e / 2, e) u = 1 ↔ oldPointDifference e u < 0 := by
    simp only [translatedSavingChi, savingChi, one_mul,
      oldPointDifference, sub_lt_zero]
    split_ifs <;> simp_all
  simp only [mem_ofPred_eq, hchi]
  constructor
  · rintro ⟨hu, h⟩
    exact (oldPointDifference_neg_iff he he1 hu).mp h
  · intro hu
    have h01 : u ∈ Ico (0 : ℝ) 1 := by
      rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
    exact ⟨h01, (oldPointDifference_neg_iff he he1 h01).mpr hu⟩

/--
@isnad1 id=eq.2h1v.s6.3ca13b25742c from=translated src=- shape=2970085c vocab=718e77a8
-/
theorem oldPoint_measure {e : ℝ} (he : 0 ≤ e) (he1 : e < 1 / 15) :
    translatedSavingMeasure 1 2 3 (e / 2, e) = 1 / 6 + e := by
  let S : Set ℝ := Ico (1 / 2 - e / 2) (2 / 3) ∪ Ico (1 - e / 2) 1
  have hS : MeasurableSet S := measurableSet_Ico.union measurableSet_Ico
  have hsub : S ⊆ Ico (0 : ℝ) 1 := by
    rintro u (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> constructor <;> linarith
  have hdisj : Disjoint (Ico (1 / 2 - e / 2) (2 / 3)) (Ico (1 - e / 2) 1) := by
    apply disjoint_left.mpr
    rintro u ⟨h1, h2⟩ ⟨h3, h4⟩
    linarith
  have hind : ∀ u ∈ Ico (0 : ℝ) 1,
      translatedSavingChi 1 2 3 (e / 2, e) u = S.indicator (fun _ => (1 : ℝ)) u := by
    intro u hu
    have hiff := oldPointDifference_neg_iff he he1 hu
    change oldPointDifference e u < 0 ↔ u ∈ S at hiff
    unfold translatedSavingChi savingChi
    dsimp only
    rw [one_mul]
    simp only [oldPointDifference, sub_lt_zero] at hiff
    simp only [hiff]
    by_cases h : u ∈ S <;> simp [h]
  calc
    _ = ∫ u in Ico (0 : ℝ) 1, S.indicator (fun _ => (1 : ℝ)) u := by
      unfold translatedSavingMeasure
      rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Ico_eq_integral_Ioc]
      exact setIntegral_congr_fun measurableSet_Ico hind
    _ = ∫ _u in S, (1 : ℝ) := by rw [setIntegral_indicator hS, inter_eq_right.mpr hsub]
    _ = (∫ _u in Ico (1 / 2 - e / 2) (2 / 3), (1 : ℝ)) +
        ∫ _u in Ico (1 - e / 2) 1, (1 : ℝ) := by
      exact setIntegral_union hdisj measurableSet_Ico
        (integrableOn_const (by simp)) (integrableOn_const (by simp))
    _ = _ := by
      rw [setIntegral_const, setIntegral_const]
      simp only [smul_eq_mul, mul_one, Real.volume_real_Ico,
        max_eq_left (show (0 : ℝ) ≤ 2 / 3 - (1 / 2 - e / 2) by linarith),
        max_eq_left (show (0 : ℝ) ≤ 1 - (1 - e / 2) by linarith)]
      ring

/--
@isnad1 id=eq.0h0v.s5.6e83b1767e1c from=translated src=- shape=b1dd3a6b vocab=f499effc
-/
theorem oldPoint_measure_zero : translatedSavingMeasure 1 2 3 0 = (1 : ℝ) / 6 := by
  change translatedSavingMeasure 1 2 3 (0, 0) = _
  simpa using oldPoint_measure (e := 0) (by norm_num) (by norm_num)

/--
@isnad1 id=eq.2h1v.s7.fa9377926224 from=translated src=- shape=5d2ca483 vocab=0e7b696c
-/
theorem oldPoint_measure_direction {e : ℝ} (he : 0 ≤ e) (he1 : e < 1 / 15) :
    translatedSavingMeasure 1 2 3 (e • ((1 : ℝ) / 2, 1)) -
      translatedSavingMeasure 1 2 3 0 = e := by
  have hpair : e • ((1 : ℝ) / 2, 1) = (e / 2, e) := by ext <;> simp [div_eq_mul_inv]
  rw [hpair, oldPoint_measure he he1, oldPoint_measure_zero]
  ring

end PiIrrationality
