import Tengoku.Piirrationalitymeasure.Formalization.PrimeSavingMeasure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The 2784 intervals are exactly the connected components of the saving set. -/

namespace PiIrrationality

theorem savingInterval_subset_set {j : ℕ} (hj : j ∈ activeSavingCells) :
    savingInterval j ⊆ primeSavingSet := by
  rw [primeSavingSet_eq_intervals]
  exact Set.subset_iUnion_of_subset j (Set.subset_iUnion_of_subset hj Set.Subset.rfl)

theorem savingRight_not_mem {j : ℕ} (hj : j ∈ activeSavingCells) :
    savingRight j ∉ primeSavingSet := by
  have he := savingInterval_endpoints hj
  have hcell : SavingCell j (savingRight j) := by
    constructor <;> dsimp [savingLeft] at he <;> linarith [he.2.1, he.2.2.1]
  have hj' : j ≤ 3713 := by have := mem_activeSavingCells.mp hj; omega
  intro h
  exact (lt_irrefl _) ((savingCell_condition_classification hj' hcell).mp h.2.2).2

theorem savingIntervals_strict_gap {i j : ℕ}
    (hi : i ∈ activeSavingCells) (hij : i < j) : savingRight i < savingLeft j := by
  have he := (savingInterval_endpoints hi).2.2.1
  have hgap : (i : ℝ) + 1 ≤ j := by exact_mod_cast (show i + 1 ≤ j by omega)
  dsimp [savingLeft]
  linarith

theorem savingInterval_connectedComponent {j : ℕ} (hj : j ∈ activeSavingCells)
    {u : ℝ} (hu : u ∈ savingInterval j) :
    connectedComponentIn primeSavingSet u = savingInterval j := by
  have hue : u ∈ primeSavingSet := savingInterval_subset_set hj hu
  have huc : u ∈ connectedComponentIn primeSavingSet u := mem_connectedComponentIn hue
  apply Set.Subset.antisymm
  · intro v hv
    have hve := connectedComponentIn_subset primeSavingSet u hv
    rw [primeSavingSet_eq_intervals] at hve
    obtain ⟨k, hve⟩ := Set.mem_iUnion.mp hve
    obtain ⟨hk, hvk⟩ := Set.mem_iUnion.mp hve
    by_cases hkj : k = j
    · simpa only [hkj] using hvk
    exfalso
    rcases lt_or_gt_of_ne hkj with hkj | hjk
    · have hgap := savingIntervals_strict_gap hk hkj
      have hr : savingRight k ∈ connectedComponentIn primeSavingSet u :=
        isPreconnected_connectedComponentIn.Icc_subset hv huc
          ⟨hvk.2.le, le_trans hgap.le hu.1⟩
      exact savingRight_not_mem hk (connectedComponentIn_subset primeSavingSet u hr)
    · have hgap := savingIntervals_strict_gap hj hjk
      have hr : savingRight j ∈ connectedComponentIn primeSavingSet u :=
        isPreconnected_connectedComponentIn.Icc_subset huc hv
          ⟨hu.2.le, le_trans hgap.le hvk.1⟩
      exact savingRight_not_mem hj (connectedComponentIn_subset primeSavingSet u hr)
  · exact isPreconnected_Ico.subset_connectedComponentIn hu (savingInterval_subset_set hj)

theorem savingInterval_injOn :
    Set.InjOn savingInterval (↑activeSavingCells : Set ℕ) := by
  intro i hi j hj heq
  by_contra hne
  have hdis := savingIntervals_pairwiseDisjoint hi hj hne
  have hmem : savingLeft i ∈ savingInterval i :=
    ⟨le_rfl, (savingInterval_endpoints hi).2.1⟩
  exact Set.disjoint_left.mp hdis hmem (heq ▸ hmem)

theorem primeSavingSet_components :
    {s : Set ℝ | ∃ u ∈ primeSavingSet, connectedComponentIn primeSavingSet u = s} =
      savingInterval '' (↑activeSavingCells : Set ℕ) := by
  ext s
  constructor
  · rintro ⟨u, hue, rfl⟩
    rw [primeSavingSet_eq_intervals] at hue
    obtain ⟨j, hue⟩ := Set.mem_iUnion.mp hue
    obtain ⟨hj, hu⟩ := Set.mem_iUnion.mp hue
    exact ⟨j, hj, (savingInterval_connectedComponent hj hu).symm⟩
  · rintro ⟨j, hj, rfl⟩
    have hu : savingLeft j ∈ savingInterval j :=
      ⟨le_rfl, (savingInterval_endpoints hj).2.1⟩
    exact ⟨savingLeft j, savingInterval_subset_set hj hu,
      savingInterval_connectedComponent hj hu⟩

theorem primeSavingSet_component_count :
    {s : Set ℝ | ∃ u ∈ primeSavingSet, connectedComponentIn primeSavingSet u = s}.ncard =
      2784 := by
  classical
  rw [primeSavingSet_components, ← Finset.coe_image, Set.ncard_coe_finset,
    Finset.card_image_of_injOn savingInterval_injOn, activeSavingCells_card]

end PiIrrationality
