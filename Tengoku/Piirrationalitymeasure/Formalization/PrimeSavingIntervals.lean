import Tengoku.Piirrationalitymeasure.Formalization.PrimeSavingCells

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The complete five-family decomposition in Proposition 3.1. -/

namespace PiIrrationality

def activeSavingCells : Finset ℕ := familyI ∪ familyII ∪ familyIII ∪ familyIV ∪ familyV

noncomputable def savingLeft (j : ℕ) : ℝ := (j : ℝ) / 3714

noncomputable def savingRight (j : ℕ) : ℝ :=
  if j % 2 = 0 then
    if j ≤ 1114 then 3 * (j : ℝ) / 11140 else (2 * (j : ℝ) + 1) / 7430
  else if j ≤ 371 then (3 * (j : ℝ) + 1) / 11140
  else if j ≤ 1857 then (2 * (j : ℝ) + 1) / 7430
  else (3 * (j : ℝ) - 1) / 11140

def savingInterval (j : ℕ) : Set ℝ := Set.Ico (savingLeft j) (savingRight j)

/--
@isnad1 id=iff.0h1v.s6.87c021f6b1ec from=translated src=- shape=504a63ad vocab=c74cb855
-/
theorem mem_activeSavingCells {j : ℕ} :
    j ∈ activeSavingCells ↔ (1 ≤ j ∧ j ≤ 1856) ∨ (1859 ≤ j ∧ j ≤ 3713 ∧ j % 2 = 1) := by
  simp only [activeSavingCells, familyI, familyII, familyIII, familyIV, familyV,
    Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
  omega

/--
@isnad1 id=eq.1h1v.s6.b1d71171821d from=translated src=- shape=d2acc5c7 vocab=04cd99b8
-/
theorem savingRight_familyI {j : ℕ} (hj : j ∈ familyI) :
    savingRight j = (3 * (j : ℝ) + 1) / 11140 := by
  simp only [familyI, Finset.mem_filter, Finset.mem_Icc] at hj
  simp [savingRight, hj.2, hj.1.2]

/--
@isnad1 id=eq.1h1v.s5.c260817484e6 from=translated src=- shape=58b15b8d vocab=83743f78
-/
theorem savingRight_familyII {j : ℕ} (hj : j ∈ familyII) :
    savingRight j = 3 * (j : ℝ) / 11140 := by
  simp only [familyII, Finset.mem_filter, Finset.mem_Icc] at hj
  simp [savingRight, hj.2, hj.1.2]

/--
@isnad1 id=eq.1h1v.s6.bcc0578464e9 from=translated src=- shape=d2acc5c7 vocab=2a2cf875
-/
theorem savingRight_familyIII {j : ℕ} (hj : j ∈ familyIII) :
    savingRight j = (2 * (j : ℝ) + 1) / 7430 := by
  simp only [familyIII, Finset.mem_filter, Finset.mem_Icc] at hj
  simp [savingRight, hj.2, show ¬j ≤ 371 by omega, show j ≤ 1857 by omega]

/--
@isnad1 id=eq.1h1v.s6.0db822e5d309 from=translated src=- shape=d2acc5c7 vocab=7fc498bc
-/
theorem savingRight_familyIV {j : ℕ} (hj : j ∈ familyIV) :
    savingRight j = (2 * (j : ℝ) + 1) / 7430 := by
  simp only [familyIV, Finset.mem_filter, Finset.mem_Icc] at hj
  simp [savingRight, hj.2, show ¬j ≤ 1114 by omega]

/--
@isnad1 id=eq.1h1v.s6.f28e5695df5a from=translated src=- shape=d2acc5c7 vocab=af27822d
-/
theorem savingRight_familyV {j : ℕ} (hj : j ∈ familyV) :
    savingRight j = (3 * (j : ℝ) - 1) / 11140 := by
  simp only [familyV, Finset.mem_filter, Finset.mem_Icc] at hj
  simp [savingRight, hj.2, show ¬j ≤ 371 by omega, show ¬j ≤ 1857 by omega]

/--
@isnad1 id=iff.2h2v.s5.6be55e1c53b1 from=translated src=- shape=a4e9387f vocab=a8279936
-/
theorem savingCell_condition_classification {j : ℕ} {u : ℝ}
    (hj : j ≤ 3713) (hu : SavingCell j u) :
    primeSavingCondition u ↔ j ∈ activeSavingCells ∧ u < savingRight j := by
  by_cases hz : j = 0
  · subst j
    simp [savingCell_zero hu, mem_activeSavingCells]
  have hjpos : 1 ≤ j := by omega
  have hu₀ := hu.1
  have hhigh : (j : ℝ) ≤ 3713 := by exact_mod_cast hj
  by_cases he : j % 2 = 0
  · rw [savingCell_condition_even hjpos hj he hu]
    by_cases hl : j ≤ 1114
    · have hm : j ∈ activeSavingCells := mem_activeSavingCells.mpr (Or.inl ⟨hjpos, by omega⟩)
      simp only [hm, savingRight, he, hl, ite_true, true_and]
      have hl' : (j : ℝ) ≤ 1114 := by exact_mod_cast hl
      constructor
      · exact And.left
      · intro h
        exact ⟨h, by linarith⟩
    · simp only [savingRight, he, hl, ite_true, ite_false]
      by_cases hm : j ≤ 1856
      · have hmem : j ∈ activeSavingCells := mem_activeSavingCells.mpr (Or.inl ⟨hjpos, hm⟩)
        simp only [hmem, true_and]
        have hl' : (1114 : ℝ) < j := by exact_mod_cast (show 1114 < j by omega)
        constructor
        · exact And.right
        · intro h
          exact ⟨by linarith, h⟩
      · have hmem : j ∉ activeSavingCells := by rw [mem_activeSavingCells]; omega
        simp only [hmem, false_and, iff_false]
        have hl' : (1858 : ℝ) ≤ j := by exact_mod_cast (show 1858 ≤ j by omega)
        rintro ⟨h₁, h₂⟩
        linarith
  · have ho : j % 2 = 1 := by omega
    by_cases hl : j ≤ 1857
    · rw [savingCell_condition_lower_odd hl ho hu]
      by_cases hs : j ≤ 371
      · have hm : j ∈ activeSavingCells := mem_activeSavingCells.mpr (Or.inl ⟨hjpos, by omega⟩)
        simp only [hm, savingRight, he, hs, ite_false, ite_true, true_and]
        have hs' : (j : ℝ) ≤ 371 := by exact_mod_cast hs
        constructor
        · exact And.left
        · intro h
          exact ⟨h, by linarith⟩
      · simp only [savingRight, he, hs, hl, ite_false, ite_true]
        by_cases hm : j ≤ 1856
        · have hmem : j ∈ activeSavingCells := mem_activeSavingCells.mpr (Or.inl ⟨hjpos, hm⟩)
          simp only [hmem, true_and]
          have hs' : (371 : ℝ) < j := by exact_mod_cast (show 371 < j by omega)
          constructor
          · exact And.right
          · intro h
            exact ⟨by linarith, h⟩
        · have heq : j = 1857 := by omega
          subst j
          norm_num [mem_activeSavingCells] at *
          intro h₁
          linarith
    · have hl' : 1859 ≤ j := by omega
      rw [savingCell_condition_upper_odd hl' hj ho hu]
      have hm : j ∈ activeSavingCells := mem_activeSavingCells.mpr (Or.inr ⟨hl', hj, ho⟩)
      simp [hm, savingRight, he, hl, show ¬j ≤ 371 by omega]

/--
@isnad1 id=and.1h1v.s6.0ec250153268 from=translated src=- shape=b7ae6360 vocab=f27498ec
-/
theorem savingInterval_endpoints {j : ℕ} (hj : j ∈ activeSavingCells) :
    0 < savingLeft j ∧ savingLeft j < savingRight j ∧
      savingRight j < ((j : ℝ) + 1) / 3714 ∧ savingRight j < 1 := by
  have hb := mem_activeSavingCells.mp hj
  have hlow : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
  have hhigh : (j : ℝ) ≤ 3713 := by exact_mod_cast (show j ≤ 3713 by omega)
  simp only [savingLeft, savingRight]
  split_ifs with he hl hs hm
  all_goals
    first
    | have h₁ : (j : ℝ) ≤ 1114 := by exact_mod_cast hl
      constructor; linarith
      constructor; linarith
      constructor <;> linarith
    | have h₁ : (j : ℝ) ≤ 1856 := by exact_mod_cast (show j ≤ 1856 by omega)
      have h₂ : (1114 : ℝ) < j := by exact_mod_cast (show 1114 < j by omega)
      constructor; linarith
      constructor; linarith
      constructor <;> linarith
    | have h₁ : (j : ℝ) ≤ 371 := by exact_mod_cast hs
      constructor; linarith
      constructor; linarith
      constructor <;> linarith
    | have h₁ : (j : ℝ) ≤ 1856 := by exact_mod_cast (show j ≤ 1856 by omega)
      constructor; linarith
      constructor; linarith
      constructor <;> linarith
    | have h₁ : (1859 : ℝ) ≤ j := by exact_mod_cast (show 1859 ≤ j by omega)
      constructor; linarith
      constructor; linarith
      constructor <;> linarith

/--
@isnad1 id=savingce.2h2v.s4.dd786531f125 from=translated src=- shape=ff17faa5 vocab=dd3d426f
-/
theorem savingInterval_subset_cell {j : ℕ} (hj : j ∈ activeSavingCells)
    {u : ℝ} (hu : u ∈ savingInterval j) : SavingCell j u := by
  have he := savingInterval_endpoints hj
  change (j : ℝ) / 3714 ≤ u ∧ u < savingRight j at hu
  constructor <;> linarith [hu.1, hu.2, he.2.2.1]

/--
@isnad1 id=eq.0h0v.s5.d9826c6303ed from=translated src=- shape=8a42282a vocab=0e78a104
-/
theorem primeSavingSet_eq_intervals :
    primeSavingSet = ⋃ j ∈ activeSavingCells, savingInterval j := by
  ext u
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨hu₀, hu₁, hc⟩
    let j := ⌊3714 * u⌋₊
    have hnonneg : 0 ≤ 3714 * u := by positivity
    have hcell : SavingCell j u := ⟨Nat.floor_le hnonneg, Nat.lt_floor_add_one _⟩
    have hj : j ≤ 3713 := by
      have hlt : j < 3714 := (Nat.floor_lt hnonneg).mpr (by norm_num; linarith)
      omega
    obtain ⟨hm, hr⟩ := (savingCell_condition_classification hj hcell).mp hc
    refine ⟨j, hm, ?_⟩
    exact ⟨by dsimp [savingLeft]; linarith [hcell.1], hr⟩
  · rintro ⟨j, hj, hu⟩
    have he := savingInterval_endpoints hj
    have hcell := savingInterval_subset_cell hj hu
    have hj' : j ≤ 3713 := by have := mem_activeSavingCells.mp hj; omega
    exact ⟨le_trans he.1.le hu.1, lt_trans hu.2 he.2.2.2,
      (savingCell_condition_classification hj' hcell).mpr ⟨hj, hu.2⟩⟩

/--
@isnad1 id=pairwise.0h0v.s5.f8451a0129f9 from=translated src=- shape=e41f8840 vocab=b8141332
-/
theorem savingIntervals_pairwiseDisjoint :
    Set.PairwiseDisjoint (↑activeSavingCells : Set ℕ) savingInterval := by
  intro i hi j hj hne
  apply Set.disjoint_left.mpr
  intro u hui huj
  have hci := savingInterval_subset_cell hi hui
  have hcj := savingInterval_subset_cell hj huj
  have hfi := savingCell_floor_b hci
  have hfj := savingCell_floor_b hcj
  exact hne (by exact_mod_cast hfi.symm.trans hfj)

/--
@isnad1 id=eq.0h0v.s9.971c17295db4 from=translated src=- shape=6efc6df6 vocab=6274ac45
-/
theorem primeSavingSet_five_families :
    primeSavingSet =
      (⋃ j ∈ familyI, Set.Ico ((j : ℝ) / 3714) ((3 * (j : ℝ) + 1) / 11140)) ∪
      (⋃ j ∈ familyII, Set.Ico ((j : ℝ) / 3714) (3 * (j : ℝ) / 11140)) ∪
      (⋃ j ∈ familyIII, Set.Ico ((j : ℝ) / 3714) ((2 * (j : ℝ) + 1) / 7430)) ∪
      (⋃ j ∈ familyIV, Set.Ico ((j : ℝ) / 3714) ((2 * (j : ℝ) + 1) / 7430)) ∪
      (⋃ j ∈ familyV, Set.Ico ((j : ℝ) / 3714) ((3 * (j : ℝ) - 1) / 11140)) := by
  have hI : (⋃ j ∈ familyI, savingInterval j) =
      ⋃ j ∈ familyI, Set.Ico ((j : ℝ) / 3714) ((3 * (j : ℝ) + 1) / 11140) := by
    apply Set.iUnion_congr
    intro j
    apply Set.iUnion_congr
    intro hj
    rw [savingInterval, savingLeft, savingRight_familyI hj]
  have hII : (⋃ j ∈ familyII, savingInterval j) =
      ⋃ j ∈ familyII, Set.Ico ((j : ℝ) / 3714) (3 * (j : ℝ) / 11140) := by
    apply Set.iUnion_congr
    intro j
    apply Set.iUnion_congr
    intro hj
    rw [savingInterval, savingLeft, savingRight_familyII hj]
  have hIII : (⋃ j ∈ familyIII, savingInterval j) =
      ⋃ j ∈ familyIII, Set.Ico ((j : ℝ) / 3714) ((2 * (j : ℝ) + 1) / 7430) := by
    apply Set.iUnion_congr
    intro j
    apply Set.iUnion_congr
    intro hj
    rw [savingInterval, savingLeft, savingRight_familyIII hj]
  have hIV : (⋃ j ∈ familyIV, savingInterval j) =
      ⋃ j ∈ familyIV, Set.Ico ((j : ℝ) / 3714) ((2 * (j : ℝ) + 1) / 7430) := by
    apply Set.iUnion_congr
    intro j
    apply Set.iUnion_congr
    intro hj
    rw [savingInterval, savingLeft, savingRight_familyIV hj]
  have hV : (⋃ j ∈ familyV, savingInterval j) =
      ⋃ j ∈ familyV, Set.Ico ((j : ℝ) / 3714) ((3 * (j : ℝ) - 1) / 11140) := by
    apply Set.iUnion_congr
    intro j
    apply Set.iUnion_congr
    intro hj
    rw [savingInterval, savingLeft, savingRight_familyV hj]
  rw [← hI, ← hII, ← hIII, ← hIV, ← hV, primeSavingSet_eq_intervals]
  ext u
  simp only [activeSavingCells, Set.mem_iUnion, Set.mem_union, Finset.mem_union,
    exists_prop, or_and_right, exists_or]

end PiIrrationality
