import Tengoku.Piirrationalitymeasure.Formalization.SavingCellGeometry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! A fixed finite floor partition expresses the translated measure using clipped affine lengths. -/

namespace PiIrrationality

open MeasureTheory Set

noncomputable def savingFloorWindow (a : ℝ) : Finset ℤ := Finset.Icc (-2) (⌈a⌉ + 2)

noncomputable def savingCellIndices (a b c : ℝ) : Finset (ℤ × ℤ × ℤ) :=
  (savingFloorWindow a).product ((savingFloorWindow b).product (savingFloorWindow c))

/--
@isnad1 id=mem.4h3v.s6.85de1263fd03 from=translated src=- shape=5491060c vocab=90e383d7
-/
theorem floor_mem_savingFloorWindow {a u d : ℝ} (ha : 0 ≤ a)
    (hu : u ∈ Ico (0 : ℝ) 1) (hd0 : -1 ≤ d) (hd1 : d ≤ 2) :
    ⌊a * u + d⌋ ∈ savingFloorWindow a := by
  rw [savingFloorWindow, Finset.mem_Icc]
  constructor
  · apply Int.le_floor.mpr
    norm_num only [Int.cast_neg, Int.cast_ofNat]
    nlinarith [mul_nonneg ha hu.1]
  · calc
      ⌊a * u + d⌋ ≤ ⌊((⌈a⌉ + 2 : ℤ) : ℝ)⌋ := Int.floor_mono (by
        push_cast
        have hau := mul_le_mul_of_nonneg_left hu.2.le ha
        linarith [Int.le_ceil a])
      _ = _ := Int.floor_intCast _

/--
@isnad1 id=mem.5h5v.s7.f1c2a0da2449 from=translated src=- shape=768c805d vocab=a2e86de4
-/
theorem savingCell_actual_index_mem {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    {z : ℝ × ℝ} (hz : parameterNormOne z ≤ 1) {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) :
    (⌊a * u + z.1 + 1 / 2⌋, ⌊b * u + z.2⌋, ⌊c * u⌋) ∈ savingCellIndices a b c := by
  have hx0 := neg_abs_le z.1
  have hx1 := le_abs_self z.1
  have hy0 := neg_abs_le z.2
  have hy1 := le_abs_self z.2
  have hxabs := abs_nonneg z.1
  have hyabs := abs_nonneg z.2
  dsimp [parameterNormOne] at hz
  apply Finset.mem_product.mpr
  refine ⟨?_, Finset.mem_product.mpr
    ⟨floor_mem_savingFloorWindow hb hu (by linarith) (by linarith), ?_⟩⟩
  · simpa only [add_assoc] using
      floor_mem_savingFloorWindow ha hu
        (show -1 ≤ z.1 + 1 / 2 by linarith) (show z.1 + 1 / 2 ≤ 2 by linarith)
  · simpa only [add_zero] using
      floor_mem_savingFloorWindow hc hu (d := 0) (by norm_num) (by norm_num)

/--
@isnad1 id=eq.5h5v.s7.21f5558ace76 from=translated src=- shape=dd2a146d vocab=f7c84257
-/
theorem translatedSavingChi_eq_cell_sum {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    {z : ℝ × ℝ} (hz : parameterNormOne z ≤ 1) {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) :
    translatedSavingChi a b c z u =
      ∑ p ∈ savingCellIndices a b c,
        (savingCell a b c z p.1 p.2.1 p.2.2).indicator (fun _ => (1 : ℝ)) u := by
  classical
  let p : ℤ × ℤ × ℤ := (⌊a * u + z.1 + 1 / 2⌋, ⌊b * u + z.2⌋, ⌊c * u⌋)
  have hp : p ∈ savingCellIndices a b c := savingCell_actual_index_mem ha hb hc hz hu
  rw [Finset.sum_eq_single p]
  · have hmem : u ∈ savingCell a b c z p.1 p.2.1 p.2.2 ↔
        translatedSavingChi a b c z u = 1 := by
      rw [savingCell_mem_iff]
      simp [p, hu]
    by_cases hchi : translatedSavingChi a b c z u = 1
    · rw [hchi, Set.indicator_of_mem (hmem.mpr hchi)]
    · rw [Set.indicator_of_notMem (fun h => hchi (hmem.mp h))]
      unfold translatedSavingChi savingChi at hchi ⊢
      split_ifs at * <;> simp_all
  · intro q hq hqp
    apply Set.indicator_of_notMem
    intro hmem
    obtain ⟨_, hA, hB, hC, _⟩ := (savingCell_mem_iff a b c z q.1 q.2.1 q.2.2 u).mp hmem
    exact hqp (Prod.ext hA.symm (Prod.ext hB.symm hC.symm))
  · intro hnot
    exact (hnot hp).elim

/--
@isnad1 id=eq.5h4v.s7.f7888c71f949 from=translated src=- shape=91a1bb4b vocab=3092caa9
-/
theorem translatedSavingMeasure_eq_cell_sum {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hq : a + 2 * b - c ≠ 0)
    {z : ℝ × ℝ} (hz : parameterNormOne z ≤ 1) :
    translatedSavingMeasure a b c z =
      ∑ p ∈ savingCellIndices a b c,
        max 0 (savingCellUpper a b c z p.1 p.2.1 p.2.2 -
          savingCellLower a b c z p.1 p.2.1 p.2.2) := by
  let F : (ℤ × ℤ × ℤ) → ℝ → ℝ := fun p =>
    (savingCell a b c z p.1 p.2.1 p.2.2).indicator (fun _ => (1 : ℝ))
  have hi (p : ℤ × ℤ × ℤ) : IntegrableOn (F p) (Ico (0 : ℝ) 1) :=
    (integrableOn_const (by simp) : IntegrableOn (fun _ : ℝ => (1 : ℝ))
      (Ico (0 : ℝ) 1)).indicator (savingCell_measurable a b c z p.1 p.2.1 p.2.2)
  calc
    _ = ∫ u in Ico (0 : ℝ) 1, ∑ p ∈ savingCellIndices a b c, F p u := by
      unfold translatedSavingMeasure
      rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Ico_eq_integral_Ioc]
      apply setIntegral_congr_fun measurableSet_Ico
      intro u hu
      exact translatedSavingChi_eq_cell_sum ha.le hb.le hc.le hz hu
    _ = ∑ p ∈ savingCellIndices a b c, ∫ u in Ico (0 : ℝ) 1, F p u :=
      integral_finsetSum _ (fun p _ => hi p)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      have hsub : savingCell a b c z p.1 p.2.1 p.2.2 ⊆ Ico (0 : ℝ) 1 :=
        fun _ h => ⟨h.1, h.2.1⟩
      dsimp only [F]
      rw [setIntegral_indicator (savingCell_measurable a b c z p.1 p.2.1 p.2.2),
        inter_eq_right.mpr hsub, setIntegral_const, smul_eq_mul, mul_one,
        savingCell_volume_real ha hb hc hq]

end PiIrrationality
