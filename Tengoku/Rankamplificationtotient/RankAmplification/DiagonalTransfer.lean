import Tengoku.Rankamplificationtotient.RankAmplification.DiagonalSkeleton
import Tengoku.Rankamplificationtotient.RankAmplification.RankStrata
import Tengoku.Rankamplificationtotient.RankAmplification.Elementary

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Exact transfer with the diagonal displayed This file formalizes the finite set and cardinality layer of Proposition 9.7. -/

namespace RankAmplification

/-- The off-diagonal nonsmooth remainder `E_h(x;y)` as a finite set.-/
noncomputable def offDiagonalNonsmoothSet (x h y : ℕ) : Finset ℕ :=
  nonsmoothShiftedSet x h y \ aboveCutoffDiagonalSet x h y

/-- The exact cardinality of the off-diagonal nonsmooth remainder.-/
noncomputable def offDiagonalNonsmoothCount (x h y : ℕ) : ℕ :=
  (offDiagonalNonsmoothSet x h y).card

@[simp]
theorem mem_offDiagonalNonsmoothSet {x h y n : ℕ} :
    n ∈ offDiagonalNonsmoothSet x h y ↔
      n ∈ nonsmoothShiftedSet x h y ∧ n ∉ aboveCutoffDiagonalSet x h y := by
  classical
  simp [offDiagonalNonsmoothSet]

/-- Fully expanded membership API for the off-diagonal remainder.-/
theorem mem_offDiagonalNonsmoothSet_iff {x h y n : ℕ} :
    n ∈ offDiagonalNonsmoothSet x h y ↔
      1 ≤ n ∧ n ≤ x ∧ n.totient = (n + h).totient ∧
        y < largestPrimeFactor n.totient ∧ ¬IsAboveCutoffDiagonal h y n := by
  rw [mem_offDiagonalNonsmoothSet, mem_nonsmoothShiftedSet]
  constructor
  · rintro ⟨⟨hn, hnx, heq, hcut⟩, hnotDiagonal⟩
    refine ⟨hn, hnx, heq, hcut, ?_⟩
    intro hdiag
    apply hnotDiagonal
    exact mem_aboveCutoffDiagonalSet.mpr ⟨hn, hnx, hdiag⟩
  · rintro ⟨hn, hnx, heq, hcut, hnotDiagonal⟩
    refine ⟨⟨hn, hnx, heq, hcut⟩, ?_⟩
    intro hmem
    exact hnotDiagonal (mem_aboveCutoffDiagonalSet.mp hmem).2.2

/-- Proposition 9.7's first assertion: the displayed diagonal is contained in the nonsmooth shifted set.-/
theorem diagonalSet_subset_nonsmoothShiftedSet (x h y : ℕ) :
    aboveCutoffDiagonalSet x h y ⊆ nonsmoothShiftedSet x h y :=
  aboveCutoffDiagonalSet_subset_nonsmoothShiftedSet x h y

/-- The off-diagonal remainder is contained in the nonsmooth shifted set.-/
theorem offDiagonalNonsmoothSet_subset_nonsmoothShiftedSet (x h y : ℕ) :
    offDiagonalNonsmoothSet x h y ⊆ nonsmoothShiftedSet x h y := by
  exact Finset.sdiff_subset

/-- The diagonal and the off-diagonal remainder are disjoint.-/
theorem aboveCutoffDiagonalSet_disjoint_offDiagonalNonsmoothSet (x h y : ℕ) :
    Disjoint (aboveCutoffDiagonalSet x h y) (offDiagonalNonsmoothSet x h y) := by
  exact Finset.disjoint_sdiff

/-- Exact set partition underlying Proposition 9.7.-/
theorem aboveCutoffDiagonalSet_union_offDiagonalNonsmoothSet (x h y : ℕ) :
    aboveCutoffDiagonalSet x h y ∪ offDiagonalNonsmoothSet x h y =
      nonsmoothShiftedSet x h y := by
  exact Finset.union_sdiff_of_subset (diagonalSet_subset_nonsmoothShiftedSet x h y)

/-- Exact cardinality identity `B_h = D_h + E_h`.-/
theorem nonsmoothShiftedCount_eq_aboveCutoffDiagonalCount_add_offDiagonalNonsmoothCount
    (x h y : ℕ) :
    nonsmoothShiftedCount x h y =
      aboveCutoffDiagonalCount x h y + offDiagonalNonsmoothCount x h y := by
  rw [nonsmoothShiftedCount,
    ← aboveCutoffDiagonalSet_union_offDiagonalNonsmoothSet x h y,
    Finset.card_union_of_disjoint
      (aboveCutoffDiagonalSet_disjoint_offDiagonalNonsmoothSet x h y),
    aboveCutoffDiagonalCount, offDiagonalNonsmoothCount]

/-- Difference form of the exact identity: `B_h - D_h = E_h`.-/
theorem nonsmoothShiftedCount_sub_aboveCutoffDiagonalCount (x h y : ℕ) :
    nonsmoothShiftedCount x h y - aboveCutoffDiagonalCount x h y =
      offDiagonalNonsmoothCount x h y := by
  rw [nonsmoothShiftedCount, aboveCutoffDiagonalCount, offDiagonalNonsmoothCount,
    offDiagonalNonsmoothSet]
  exact (Finset.card_sdiff_of_subset
    (diagonalSet_subset_nonsmoothShiftedSet x h y)).symm

/-- Both inequalities in the finite form of (9.4), together with its exact difference identity.-/
theorem offDiagonalNonsmooth_cardinality_equation (x h y : ℕ) :
    aboveCutoffDiagonalCount x h y ≤ nonsmoothShiftedCount x h y ∧
      0 ≤ nonsmoothShiftedCount x h y - aboveCutoffDiagonalCount x h y ∧
      nonsmoothShiftedCount x h y - aboveCutoffDiagonalCount x h y =
        offDiagonalNonsmoothCount x h y := by
  exact ⟨aboveCutoffDiagonalCount_le_nonsmoothShiftedCount x h y, Nat.zero_le _,
    nonsmoothShiftedCount_sub_aboveCutoffDiagonalCount x h y⟩

/-- The off-diagonal remainder never exceeds the full nonsmooth count.-/
theorem offDiagonalNonsmoothCount_le_nonsmoothShiftedCount (x h y : ℕ) :
    offDiagonalNonsmoothCount x h y ≤ nonsmoothShiftedCount x h y := by
  exact Finset.card_le_card (offDiagonalNonsmoothSet_subset_nonsmoothShiftedSet x h y)

/-- For a positive cutoff, the off-diagonal remainder lies in rank at least one.-/
theorem offDiagonalNonsmoothSet_subset_atLeastRankShiftedSet_one
    {x h y : ℕ} (hy : 1 ≤ y) :
    offDiagonalNonsmoothSet x h y ⊆ atLeastRankShiftedSet x h y 1 := by
  rw [atLeastRankShiftedSet_one_eq_nonsmoothShiftedSet hy]
  exact offDiagonalNonsmoothSet_subset_nonsmoothShiftedSet x h y

/-- At a positive cutoff, Proposition 9.7 is equivalently a partition of the rank-at-least-one stratum into its diagonal and off-diagonal pieces.-/
theorem aboveCutoffDiagonalSet_union_offDiagonal_eq_atLeastRankShiftedSet_one
    {x h y : ℕ} (hy : 1 ≤ y) :
    aboveCutoffDiagonalSet x h y ∪ offDiagonalNonsmoothSet x h y =
      atLeastRankShiftedSet x h y 1 := by
  calc
    aboveCutoffDiagonalSet x h y ∪ offDiagonalNonsmoothSet x h y =
        nonsmoothShiftedSet x h y :=
      aboveCutoffDiagonalSet_union_offDiagonalNonsmoothSet x h y
    _ = atLeastRankShiftedSet x h y 1 :=
      (atLeastRankShiftedSet_one_eq_nonsmoothShiftedSet hy).symm

/-- Cardinal rank-one form of the displayed-diagonal transfer identity.-/
theorem atLeastRankShiftedCount_one_eq_aboveCutoffDiagonalCount_add_offDiagonal
    {x h y : ℕ} (hy : 1 ≤ y) :
    atLeastRankShiftedCount x h y 1 =
      aboveCutoffDiagonalCount x h y + offDiagonalNonsmoothCount x h y := by
  rw [atLeastRankShiftedCount_one_eq_nonsmoothShiftedCount hy,
    nonsmoothShiftedCount_eq_aboveCutoffDiagonalCount_add_offDiagonalNonsmoothCount]

/-- The off-diagonal count is bounded by the rank-at-least-one count.-/
theorem offDiagonalNonsmoothCount_le_atLeastRankShiftedCount_one
    {x h y : ℕ} (hy : 1 ≤ y) :
    offDiagonalNonsmoothCount x h y ≤ atLeastRankShiftedCount x h y 1 := by
  exact Finset.card_le_card (offDiagonalNonsmoothSet_subset_atLeastRankShiftedSet_one hy)

/-! ## Converse diagonal parametrization inside the finite transfer -/

/-- Converse Proposition 9.4 in predicate form: a diagonal provider skeleton with prime parameter and an above-cutoff common totient is an above-cutoff diagonal integer.-/
theorem LargePrimeSkeleton.isAboveCutoffDiagonal_of_isDiagonal {h n p y : ℕ}
    (s : LargePrimeSkeleton h n p) (hp : p.Prime) (hdiag : s.IsDiagonal)
    (hcut : y < largestPrimeFactor n.totient) :
    IsAboveCutoffDiagonal h y n := by
  obtain ⟨r, hrepresentation⟩ := s.exists_diagonalRepresentation hp hdiag hcut
  exact ⟨s.m1, r, hrepresentation⟩

/-- A supplied diagonal skeleton representing a member of the nonsmooth cutoff set is captured by the finite above-cutoff diagonal set.-/
theorem LargePrimeSkeleton.mem_aboveCutoffDiagonalSet_of_isDiagonal
    {x h n p y : ℕ} (s : LargePrimeSkeleton h n p) (hp : p.Prime)
    (hdiag : s.IsDiagonal) (hnonsmooth : n ∈ nonsmoothShiftedSet x h y) :
    n ∈ aboveCutoffDiagonalSet x h y := by
  have hnData := mem_nonsmoothShiftedSet.mp hnonsmooth
  apply mem_aboveCutoffDiagonalSet.mpr
  exact ⟨hnData.1, hnData.2.1,
    s.isAboveCutoffDiagonal_of_isDiagonal hp hdiag hnData.2.2.2⟩

/-- Consequently, a diagonal skeleton can never represent a member of the off-diagonal remainder.-/
theorem LargePrimeSkeleton.not_mem_offDiagonalNonsmoothSet_of_isDiagonal
    {x h n p y : ℕ} (s : LargePrimeSkeleton h n p) (hp : p.Prime)
    (hdiag : s.IsDiagonal) :
    n ∉ offDiagonalNonsmoothSet x h y := by
  intro hn
  have hnData := mem_offDiagonalNonsmoothSet.mp hn
  exact hnData.2 (s.mem_aboveCutoffDiagonalSet_of_isDiagonal hp hdiag hnData.1)

/-- Conversely, any prime-parameter skeleton representing an element of the finite remainder is genuinely off diagonal.-/
theorem LargePrimeSkeleton.not_isDiagonal_of_mem_offDiagonalNonsmoothSet
    {x h n p y : ℕ} (s : LargePrimeSkeleton h n p) (hp : p.Prime)
    (hn : n ∈ offDiagonalNonsmoothSet x h y) :
    ¬s.IsDiagonal := by
  intro hdiag
  exact s.not_mem_offDiagonalNonsmoothSet_of_isDiagonal hp hdiag hn

/-! ## Parity consequences -/

/-- An odd shift has no diagonal provider skeleton.-/
theorem LargePrimeSkeleton.not_isDiagonal_of_odd {h n p : ℕ} (hodd : Odd h)
    (s : LargePrimeSkeleton h n p) :
    ¬s.IsDiagonal := by
  simpa only [LargePrimeSkeleton.IsDiagonal] using s.normalized_slopes_ne hodd

/-- For odd shifts the off-diagonal remainder is the entire nonsmooth set.-/
theorem offDiagonalNonsmoothSet_eq_nonsmoothShiftedSet_of_odd
    {x h y : ℕ} (hodd : Odd h) :
    offDiagonalNonsmoothSet x h y = nonsmoothShiftedSet x h y := by
  rw [offDiagonalNonsmoothSet, aboveCutoffDiagonalSet_eq_empty_of_odd hodd]
  exact Finset.sdiff_empty

/-- Count form of the odd-shift collapse of the diagonal decomposition.-/
theorem offDiagonalNonsmoothCount_eq_nonsmoothShiftedCount_of_odd
    {x h y : ℕ} (hodd : Odd h) :
    offDiagonalNonsmoothCount x h y = nonsmoothShiftedCount x h y := by
  rw [offDiagonalNonsmoothCount,
    offDiagonalNonsmoothSet_eq_nonsmoothShiftedSet_of_odd hodd,
    nonsmoothShiftedCount]

end RankAmplification
