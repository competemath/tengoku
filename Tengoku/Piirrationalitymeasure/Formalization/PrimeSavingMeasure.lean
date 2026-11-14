import Tengoku.Piirrationalitymeasure.Formalization.PrimeSavingIntervals

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Exact interval lengths and Lebesgue measure in Proposition 3.1. -/

namespace PiIrrationality

private theorem family_disjoint_I_II : Disjoint familyI familyII := by
  apply Finset.disjoint_left.mpr
  intro j hI hII
  simp only [familyI, familyII, Finset.mem_filter, Finset.mem_Icc] at *
  omega

private theorem family_disjoint_III : Disjoint (familyI ∪ familyII) familyIII := by
  apply Finset.disjoint_left.mpr
  intro j h hIII
  simp only [familyI, familyII, familyIII, Finset.mem_union, Finset.mem_filter,
    Finset.mem_Icc] at *
  omega

private theorem family_disjoint_IV : Disjoint (familyI ∪ familyII ∪ familyIII) familyIV := by
  apply Finset.disjoint_left.mpr
  intro j h hIV
  simp only [familyI, familyII, familyIII, familyIV, Finset.mem_union, Finset.mem_filter,
    Finset.mem_Icc] at *
  omega

private theorem family_disjoint_V :
    Disjoint (familyI ∪ familyII ∪ familyIII ∪ familyIV) familyV := by
  apply Finset.disjoint_left.mpr
  intro j h hV
  simp only [familyI, familyII, familyIII, familyIV, familyV, Finset.mem_union,
    Finset.mem_filter, Finset.mem_Icc] at *
  omega

/--
@isnad1 id=eq.0h0v.s3.4c2ad174698c from=translated src=- shape=3701a056 vocab=ba8e93d0
-/
theorem activeSavingCells_card : activeSavingCells.card = 2784 := by
  rw [activeSavingCells, Finset.card_union_of_disjoint family_disjoint_V,
    Finset.card_union_of_disjoint family_disjoint_IV,
    Finset.card_union_of_disjoint family_disjoint_III,
    Finset.card_union_of_disjoint family_disjoint_I_II]
  exact five_family_component_count

/--
@isnad1 id=eq.0h1v.s6.26e6633202f2 from=translated src=- shape=57ab96f5 vocab=e7d0bb9d
-/
theorem sum_activeSavingCells (f : ℕ → ℝ) :
    ∑ j ∈ activeSavingCells, f j =
      (∑ j ∈ familyI, f j) + (∑ j ∈ familyII, f j) +
      (∑ j ∈ familyIII, f j) + (∑ j ∈ familyIV, f j) + (∑ j ∈ familyV, f j) := by
  rw [activeSavingCells, Finset.sum_union family_disjoint_V,
    Finset.sum_union family_disjoint_IV, Finset.sum_union family_disjoint_III,
    Finset.sum_union family_disjoint_I_II]

private theorem indexSum_real (s : Finset ℕ) :
    (indexSum s : ℝ) = ∑ j ∈ s, (j : ℝ) := by
  simp [indexSum]

/--
@isnad1 id=eq.0h0v.s4.0345dbcb53a0 from=translated src=- shape=af3b7519 vocab=afa3fe8f
-/
theorem savingLength_familyI :
    ∑ j ∈ familyI, (savingRight j - savingLeft j) = (familyILength : ℝ) := by
  have hterm : ∀ j ∈ familyI, savingRight j - savingLeft j =
      (2 * (j : ℝ) + 3714) / (2 * 5570 * 3714) := by
    intro j hj
    rw [savingRight_familyI hj, savingLeft]
    ring
  rw [Finset.sum_congr rfl hterm]
  simp only [familyILength, Rat.cast_div, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat,
    Rat.cast_natCast, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul, indexSum_real]

/--
@isnad1 id=eq.0h0v.s4.5d3d8cfa1ed5 from=translated src=- shape=af3b7519 vocab=5e62d55a
-/
theorem savingLength_familyII :
    ∑ j ∈ familyII, (savingRight j - savingLeft j) = (familyIILength : ℝ) := by
  have hterm : ∀ j ∈ familyII, savingRight j - savingLeft j =
      (j : ℝ) / (5570 * 3714) := by
    intro j hj
    rw [savingRight_familyII hj, savingLeft]
    ring
  rw [Finset.sum_congr rfl hterm]
  simp only [familyIILength, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat,
    Rat.cast_natCast, ← Finset.sum_div, indexSum_real]

/--
@isnad1 id=eq.0h0v.s4.3d2101fb9c6f from=translated src=- shape=af3b7519 vocab=eb1b6ea4
-/
theorem savingLength_familyIII :
    ∑ j ∈ familyIII, (savingRight j - savingLeft j) = (familyIIILength : ℝ) := by
  have hterm : ∀ j ∈ familyIII, savingRight j - savingLeft j =
      (3714 - 2 * (j : ℝ)) / (2 * 3715 * 3714) := by
    intro j hj
    rw [savingRight_familyIII hj, savingLeft]
    ring
  rw [Finset.sum_congr rfl hterm]
  simp only [familyIIILength, Rat.cast_div, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat,
    Rat.cast_natCast, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul, indexSum_real]

/--
@isnad1 id=eq.0h0v.s4.85cf35942605 from=translated src=- shape=af3b7519 vocab=945e30ac
-/
theorem savingLength_familyIV :
    ∑ j ∈ familyIV, (savingRight j - savingLeft j) = (familyIVLength : ℝ) := by
  have hterm : ∀ j ∈ familyIV, savingRight j - savingLeft j =
      (3714 - 2 * (j : ℝ)) / (2 * 3715 * 3714) := by
    intro j hj
    rw [savingRight_familyIV hj, savingLeft]
    ring
  rw [Finset.sum_congr rfl hterm]
  simp only [familyIVLength, Rat.cast_div, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat,
    Rat.cast_natCast, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul, indexSum_real]

/--
@isnad1 id=eq.0h0v.s4.c0024b2c8533 from=translated src=- shape=af3b7519 vocab=8d2a2e57
-/
theorem savingLength_familyV :
    ∑ j ∈ familyV, (savingRight j - savingLeft j) = (familyVLength : ℝ) := by
  have hterm : ∀ j ∈ familyV, savingRight j - savingLeft j =
      (2 * (j : ℝ) - 3714) / (2 * 5570 * 3714) := by
    intro j hj
    rw [savingRight_familyV hj, savingLeft]
    ring
  rw [Finset.sum_congr rfl hterm]
  simp only [familyVLength, Rat.cast_div, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat,
    Rat.cast_natCast, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul, indexSum_real]

/--
@isnad1 id=eq.0h0v.s5.415875a2cbd9 from=translated src=- shape=a444b76b vocab=77bb68f8
-/
theorem savingIntervals_total_length :
    ∑ j ∈ activeSavingCells, (savingRight j - savingLeft j) =
      (1724689 : ℝ) / 13797510 := by
  rw [sum_activeSavingCells, savingLength_familyI, savingLength_familyII,
    savingLength_familyIII, savingLength_familyIV, savingLength_familyV]
  simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] using
    congrArg (fun x : ℚ => (x : ℝ)) all_family_lengths_value

/--
@isnad1 id=eq.0h0v.s5.8d80de83b773 from=translated src=- shape=349a39c5 vocab=e9a48c39
-/
theorem primeSavingSet_volume :
    MeasureTheory.volume primeSavingSet = ENNReal.ofReal ((1724689 : ℝ) / 13797510) := by
  rw [primeSavingSet_eq_intervals,
    MeasureTheory.measure_biUnion_finset savingIntervals_pairwiseDisjoint
      (fun j _ => measurableSet_Ico)]
  simp only [savingInterval, Real.volume_Ico]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j hj =>
    sub_nonneg.mpr (savingInterval_endpoints hj).2.1.le), savingIntervals_total_length]

/--
@isnad1 id=eq.0h0v.s5.a574ac010801 from=translated src=- shape=2db956ed vocab=efaf3227
-/
theorem primeSavingSet_volume_real :
    MeasureTheory.volume.real primeSavingSet = (1724689 : ℝ) / 13797510 := by
  rw [MeasureTheory.measureReal_def, primeSavingSet_volume, ENNReal.toReal_ofReal]
  positivity

/--
@isnad1 id=isleast.0h0v.s4.eb24587b546f from=translated src=- shape=0efb1284 vocab=2c41c80e
-/
theorem primeSavingSet_least : IsLeast primeSavingSet ((1 : ℝ) / 3714) := by
  have hmem : 1 ∈ activeSavingCells := mem_activeSavingCells.mpr (Or.inl ⟨by norm_num, by norm_num⟩)
  constructor
  · rw [primeSavingSet_eq_intervals]
    refine Set.mem_iUnion.mpr ⟨1, Set.mem_iUnion.mpr ⟨hmem, ?_⟩⟩
    constructor
    · norm_num [savingLeft]
    · simpa only [savingLeft, Nat.cast_one] using (savingInterval_endpoints hmem).2.1
  · intro u hu
    rw [primeSavingSet_eq_intervals] at hu
    obtain ⟨j, hu⟩ := Set.mem_iUnion.mp hu
    obtain ⟨hj, hu⟩ := Set.mem_iUnion.mp hu
    have hlow : (1 : ℝ) ≤ j := by
      exact_mod_cast (show 1 ≤ j by have := mem_activeSavingCells.mp hj; omega)
    change (j : ℝ) / 3714 ≤ u ∧ _ at hu
    linarith [hu.1]

end PiIrrationality
