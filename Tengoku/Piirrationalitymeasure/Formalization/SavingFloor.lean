import Tengoku.Piirrationalitymeasure.Formalization.ParameterSaving

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The saving indicator is determined by four floor values. -/

namespace PiIrrationality

/--
@isnad1 id=eq.0h3v.s8.364e0d9d6fa5 from=translated src=- shape=36bbdc8c vocab=5f7b8a8b
-/
theorem savingChi_floor_formula (X Y Z : ℝ) :
    savingChi X Y Z =
      if ⌊X + 2 * Y - Z + 1 / 2⌋ < ⌊X + 1 / 2⌋ + 2 * ⌊Y⌋ - ⌊Z⌋ then 1 else 0 := by
  have h : Int.fract (X + 1 / 2) + 2 * Int.fract Y < Int.fract Z ↔
      ⌊X + 2 * Y - Z + 1 / 2⌋ < ⌊X + 1 / 2⌋ + 2 * ⌊Y⌋ - ⌊Z⌋ := by
    rw [Int.floor_lt]
    simp only [Int.fract, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
    constructor <;> intro h <;> linarith
  simp only [savingChi, h]

/--
@isnad1 id=eq.4h6v.s8.d85d1a56f237 from=translated src=- shape=d7c5b4c0 vocab=b1a5a12b
-/
theorem savingChi_eq_of_floor_eq {X Y Z X' Y' Z' : ℝ}
    (hA : ⌊X + 1 / 2⌋ = ⌊X' + 1 / 2⌋) (hB : ⌊Y⌋ = ⌊Y'⌋) (hC : ⌊Z⌋ = ⌊Z'⌋)
    (hQ : ⌊X + 2 * Y - Z + 1 / 2⌋ = ⌊X' + 2 * Y' - Z' + 1 / 2⌋) :
    savingChi X Y Z = savingChi X' Y' Z' := by
  rw [savingChi_floor_formula, savingChi_floor_formula, hA, hB, hC, hQ]

noncomputable def floorDisagreement (x y : ℝ) : ℝ := if ⌊x⌋ = ⌊y⌋ then 0 else 1

/--
@isnad1 id=le.0h2v.s4.bb3a97881433 from=translated src=- shape=a120b2a8 vocab=d8abee28
-/
theorem floorDisagreement_nonneg (x y : ℝ) : 0 ≤ floorDisagreement x y := by
  unfold floorDisagreement
  split_ifs <;> norm_num

/--
@isnad1 id=le.0h2v.s4.f3a7482e924b from=translated src=- shape=aa052b1b vocab=d8abee28
-/
theorem floorDisagreement_le_one (x y : ℝ) : floorDisagreement x y ≤ 1 := by
  unfold floorDisagreement
  split_ifs <;> norm_num

/--
@isnad1 id=le.0h6v.s5.89337db4cffa from=translated src=- shape=8f750d45 vocab=d3f25a24
-/
theorem savingChi_abs_sub_le_one (X Y Z X' Y' Z' : ℝ) :
    |savingChi X Y Z - savingChi X' Y' Z'| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [savingChi_nonneg X Y Z, savingChi_le_one X Y Z,
    savingChi_nonneg X' Y' Z', savingChi_le_one X' Y' Z']

/--
@isnad1 id=le.0h6v.s7.7f9d37a356fb from=translated src=- shape=12c1300f vocab=e726f02a
-/
theorem savingChi_abs_sub_le_floorDisagreement (X Y Z X' Y' Z' : ℝ) :
    |savingChi X Y Z - savingChi X' Y' Z'| ≤
      floorDisagreement (X + 1 / 2) (X' + 1 / 2) + floorDisagreement Y Y' +
      floorDisagreement Z Z' +
      floorDisagreement (X + 2 * Y - Z + 1 / 2) (X' + 2 * Y' - Z' + 1 / 2) := by
  have hbound := savingChi_abs_sub_le_one X Y Z X' Y' Z'
  by_cases hA : ⌊X + 1 / 2⌋ = ⌊X' + 1 / 2⌋
  · by_cases hB : ⌊Y⌋ = ⌊Y'⌋
    · by_cases hC : ⌊Z⌋ = ⌊Z'⌋
      · by_cases hQ : ⌊X + 2 * Y - Z + 1 / 2⌋ = ⌊X' + 2 * Y' - Z' + 1 / 2⌋
        · rw [savingChi_eq_of_floor_eq hA hB hC hQ, sub_self, abs_zero]
          simp only [floorDisagreement, hA, hB, hC, hQ, ite_true, add_zero, le_refl]
        · simpa only [floorDisagreement, hA, hB, hC, hQ, ite_true, ite_false,
            zero_add] using hbound
      · have hQ := floorDisagreement_nonneg (X + 2 * Y - Z + 1 / 2) (X' + 2 * Y' - Z' + 1 / 2)
        simp only [floorDisagreement, hA, hB, hC, ite_true, ite_false] at *
        linarith
    · have hC := floorDisagreement_nonneg Z Z'
      have hQ := floorDisagreement_nonneg (X + 2 * Y - Z + 1 / 2) (X' + 2 * Y' - Z' + 1 / 2)
      simp only [floorDisagreement, hA, hB, ite_true, ite_false] at *
      linarith
  · have hB := floorDisagreement_nonneg Y Y'
    have hC := floorDisagreement_nonneg Z Z'
    have hQ := floorDisagreement_nonneg (X + 2 * Y - Z + 1 / 2) (X' + 2 * Y' - Z' + 1 / 2)
    simp only [floorDisagreement, hA, ite_false] at *
    linarith

/--
@isnad1 id=ex.2h3v.s5.c10bf7054e1c from=translated src=- shape=3bdc03c2 vocab=5e6dcd9b
-/
theorem floor_ne_exists_int_near {x y h : ℝ} (hxy : ⌊x⌋ ≠ ⌊y⌋) (hd : |x - y| ≤ h) :
    ∃ j : ℤ, |x - j| ≤ h := by
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · refine ⟨⌊x⌋ + 1, ?_⟩
    have hjx := Int.lt_floor_add_one x
    have hjy : ((⌊x⌋ + 1 : ℤ) : ℝ) ≤ y := Int.le_floor.mp hlt
    rw [abs_le] at hd ⊢
    push_cast at *
    constructor <;> linarith
  · refine ⟨⌊x⌋, ?_⟩
    have hjx := Int.floor_le x
    have hjy : y < (⌊x⌋ : ℝ) := Int.floor_lt.mp hgt
    rw [abs_le] at hd ⊢
    constructor <;> linarith

end PiIrrationality
