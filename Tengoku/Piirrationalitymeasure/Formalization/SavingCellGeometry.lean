import Tengoku.Piirrationalitymeasure.Formalization.SavingTranslationBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! A floor cell has measure equal to the positive part of a clipped affine interval length. -/

namespace PiIrrationality

open MeasureTheory Set

noncomputable def savingCell (a b c : ℝ) (z : ℝ × ℝ) (i j k : ℤ) : Set ℝ :=
  {u | 0 ≤ u ∧ u < 1 ∧
    (i : ℝ) ≤ a * u + z.1 + 1 / 2 ∧ a * u + z.1 + 1 / 2 < (i : ℝ) + 1 ∧
    (j : ℝ) ≤ b * u + z.2 ∧ b * u + z.2 < (j : ℝ) + 1 ∧
    (k : ℝ) ≤ c * u ∧ c * u < (k : ℝ) + 1 ∧
    (a + 2 * b - c) * u + z.1 + 2 * z.2 + 1 / 2 < (i : ℝ) + 2 * j - k}

noncomputable def savingCellThreshold (a b c : ℝ) (z : ℝ × ℝ) (i j k : ℤ) : ℝ :=
  ((i : ℝ) + 2 * j - k - 1 / 2 - z.1 - 2 * z.2) / (a + 2 * b - c)

noncomputable def savingCellLower (a b c : ℝ) (z : ℝ × ℝ) (i j k : ℤ) : ℝ :=
  max 0 (max (((i : ℝ) - 1 / 2 - z.1) / a)
    (max (((j : ℝ) - z.2) / b) (max ((k : ℝ) / c)
      (if a + 2 * b - c < 0 then savingCellThreshold a b c z i j k else 0))))

noncomputable def savingCellUpper (a b c : ℝ) (z : ℝ × ℝ) (i j k : ℤ) : ℝ :=
  min 1 (min (((i : ℝ) + 1 / 2 - z.1) / a)
    (min (((j : ℝ) + 1 - z.2) / b) (min (((k : ℝ) + 1) / c)
      (if 0 < a + 2 * b - c then savingCellThreshold a b c z i j k else 1))))

/--
@isnad1 id=measurab.0h7v.s4.c39c5e92a16b from=translated src=- shape=fbc5cb66 vocab=ca79eb34
-/
theorem savingCell_measurable (a b c : ℝ) (z : ℝ × ℝ) (i j k : ℤ) :
    MeasurableSet (savingCell a b c z i j k) := by
  unfold savingCell
  simp only [ofPred_and]
  measurability

/--
@isnad1 id=iff.0h8v.s7.10f1ecbca8f6 from=translated src=- shape=77f63ef1 vocab=0ce716e4
-/
theorem savingCell_mem_iff (a b c : ℝ) (z : ℝ × ℝ) (i j k : ℤ) (u : ℝ) :
    u ∈ savingCell a b c z i j k ↔ u ∈ Ico (0 : ℝ) 1 ∧
      ⌊a * u + z.1 + 1 / 2⌋ = i ∧ ⌊b * u + z.2⌋ = j ∧ ⌊c * u⌋ = k ∧
      translatedSavingChi a b c z u = 1 := by
  have hchi (hA : ⌊a * u + z.1 + 1 / 2⌋ = i) (hB : ⌊b * u + z.2⌋ = j)
      (hC : ⌊c * u⌋ = k) :
      translatedSavingChi a b c z u = 1 ↔
        (a + 2 * b - c) * u + z.1 + 2 * z.2 + 1 / 2 < (i : ℝ) + 2 * j - k := by
    unfold translatedSavingChi savingChi
    simp only [Int.fract, hA, hB, hC]
    split_ifs <;> norm_num <;> nlinarith
  constructor
  · rintro ⟨hu0, hu1, hA0, hA1, hB0, hB1, hC0, hC1, hq⟩
    have hA := Int.floor_eq_iff.mpr ⟨hA0, hA1⟩
    have hB := Int.floor_eq_iff.mpr ⟨hB0, hB1⟩
    have hC := Int.floor_eq_iff.mpr ⟨hC0, hC1⟩
    exact ⟨⟨hu0, hu1⟩, hA, hB, hC, (hchi hA hB hC).mpr hq⟩
  · rintro ⟨⟨hu0, hu1⟩, hA, hB, hC, h⟩
    obtain ⟨hA0, hA1⟩ := Int.floor_eq_iff.mp hA
    obtain ⟨hB0, hB1⟩ := Int.floor_eq_iff.mp hB
    obtain ⟨hC0, hC1⟩ := Int.floor_eq_iff.mp hC
    exact ⟨hu0, hu1, hA0, hA1, hB0, hB1, hC0, hC1, (hchi hA hB hC).mp h⟩

/--
@isnad1 id=le.4h7v.s6.90f8107b2b4b from=translated src=- shape=1ae566b1 vocab=9be160e2
-/
theorem savingCell_contains_open {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hq : a + 2 * b - c ≠ 0) (z : ℝ × ℝ) (i j k : ℤ) :
    Ioo (savingCellLower a b c z i j k) (savingCellUpper a b c z i j k) ⊆
      savingCell a b c z i j k := by
  rintro u ⟨hl, hr⟩
  simp only [savingCellLower, max_lt_iff] at hl
  simp only [savingCellUpper, lt_min_iff] at hr
  have hA0 := (div_lt_iff₀ ha).mp hl.2.1
  have hA1 := (lt_div_iff₀ ha).mp hr.2.1
  have hB0 := (div_lt_iff₀ hb).mp hl.2.2.1
  have hB1 := (lt_div_iff₀ hb).mp hr.2.2.1
  have hC0 := (div_lt_iff₀ hc).mp hl.2.2.2.1
  have hC1 := (lt_div_iff₀ hc).mp hr.2.2.2.1
  refine ⟨hl.1.le, hr.1, by nlinarith, by nlinarith, by nlinarith, by nlinarith,
    by nlinarith, by nlinarith, ?_⟩
  rcases lt_or_gt_of_ne hq with hneg | hpos
  · have hT : savingCellThreshold a b c z i j k < u := by simpa [hneg] using hl.2.2.2.2
    have hbound := (div_lt_iff_of_neg hneg).mp hT
    nlinarith
  · have hT : u < savingCellThreshold a b c z i j k := by simpa [hpos] using hr.2.2.2.2
    have hbound := (lt_div_iff₀ hpos).mp hT
    nlinarith

/--
@isnad1 id=le.3h7v.s6.1c15eb5f46be from=translated src=- shape=4185c5d0 vocab=9ad31b98
-/
theorem savingCell_subset_closed {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (z : ℝ × ℝ) (i j k : ℤ) :
    savingCell a b c z i j k ⊆
      Icc (savingCellLower a b c z i j k) (savingCellUpper a b c z i j k) := by
  rintro u ⟨hu0, hu1, hA0, hA1, hB0, hB1, hC0, hC1, hq⟩
  constructor
  · simp only [savingCellLower, max_le_iff]
    refine ⟨hu0, (div_le_iff₀ ha).mpr (by nlinarith),
      (div_le_iff₀ hb).mpr (by nlinarith), (div_le_iff₀ hc).mpr (by nlinarith), ?_⟩
    split_ifs with hneg
    · exact (div_le_iff_of_neg hneg).mpr (by nlinarith)
    · exact hu0
  · simp only [savingCellUpper, le_min_iff]
    refine ⟨hu1.le, (le_div_iff₀ ha).mpr (by nlinarith),
      (le_div_iff₀ hb).mpr (by nlinarith), (le_div_iff₀ hc).mpr (by nlinarith), ?_⟩
    split_ifs with hpos
    · exact (le_div_iff₀ hpos).mpr (by nlinarith)
    · exact hu1.le

/--
@isnad1 id=eq.4h7v.s7.ecb9eaccd6b0 from=translated src=- shape=0d871c3d vocab=2b790195
-/
theorem savingCell_volume {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hq : a + 2 * b - c ≠ 0) (z : ℝ × ℝ) (i j k : ℤ) :
    volume (savingCell a b c z i j k) =
      ENNReal.ofReal (savingCellUpper a b c z i j k - savingCellLower a b c z i j k) := by
  apply le_antisymm
  · calc
      volume (savingCell a b c z i j k) ≤
          volume (Icc (savingCellLower a b c z i j k) (savingCellUpper a b c z i j k)) :=
        measure_mono (savingCell_subset_closed ha hb hc z i j k)
      _ = _ := Real.volume_Icc
  · calc
      _ = volume (Ioo (savingCellLower a b c z i j k) (savingCellUpper a b c z i j k)) :=
        Real.volume_Ioo.symm
      _ ≤ volume (savingCell a b c z i j k) :=
        measure_mono (savingCell_contains_open ha hb hc hq z i j k)

/--
@isnad1 id=eq.4h7v.s7.a2781b8e519e from=translated src=- shape=d27db558 vocab=e726c346
-/
theorem savingCell_volume_real {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hq : a + 2 * b - c ≠ 0) (z : ℝ × ℝ) (i j k : ℤ) :
    volume.real (savingCell a b c z i j k) =
      max 0 (savingCellUpper a b c z i j k - savingCellLower a b c z i j k) := by
  rw [Measure.real, savingCell_volume ha hb hc hq]
  simpa only [max_comm] using (ENNReal.toReal_ofReal' (r :=
    savingCellUpper a b c z i j k - savingCellLower a b c z i j k))

end PiIrrationality
