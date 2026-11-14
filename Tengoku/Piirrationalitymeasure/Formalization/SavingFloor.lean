import Tengoku.Piirrationalitymeasure.Formalization.ParameterSaving

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The saving indicator is determined by four floor values. -/

namespace PiIrrationality

theorem savingChi_floor_formula (X Y Z : ℝ) :
    savingChi X Y Z =
      if ⌊X + 2 * Y - Z + 1 / 2⌋ < ⌊X + 1 / 2⌋ + 2 * ⌊Y⌋ - ⌊Z⌋ then 1 else 0 := by
  have h : Int.fract (X + 1 / 2) + 2 * Int.fract Y < Int.fract Z ↔
      ⌊X + 2 * Y - Z + 1 / 2⌋ < ⌊X + 1 / 2⌋ + 2 * ⌊Y⌋ - ⌊Z⌋ := by
    rw [Int.floor_lt]
    simp only [Int.fract, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
    constructor <;> intro h <;> linarith
  simp only [savingChi, h]

theorem savingChi_eq_of_floor_eq {X Y Z X' Y' Z' : ℝ}
    (hA : ⌊X + 1 / 2⌋ = ⌊X' + 1 / 2⌋) (hB : ⌊Y⌋ = ⌊Y'⌋) (hC : ⌊Z⌋ = ⌊Z'⌋)
    (hQ : ⌊X + 2 * Y - Z + 1 / 2⌋ = ⌊X' + 2 * Y' - Z' + 1 / 2⌋) :
    savingChi X Y Z = savingChi X' Y' Z' := by
  rw [savingChi_floor_formula, savingChi_floor_formula, hA, hB, hC, hQ]

noncomputable def floorDisagreement (x y : ℝ) : ℝ := if ⌊x⌋ = ⌊y⌋ then 0 else 1

theorem floorDisagreement_nonneg (x y : ℝ) : 0 ≤ floorDisagreement x y := by
  unfold floorDisagreement
  split_ifs <;> norm_num

theorem floorDisagreement_le_one (x y : ℝ) : floorDisagreement x y ≤ 1 := by
  unfold floorDisagreement
  split_ifs <;> norm_num

theorem savingChi_abs_sub_le_one (X Y Z X' Y' Z' : ℝ) :
    |savingChi X Y Z - savingChi X' Y' Z'| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [savingChi_nonneg X Y Z, savingChi_le_one X Y Z,
    savingChi_nonneg X' Y' Z', savingChi_le_one X' Y' Z']

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
