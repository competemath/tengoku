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

/--
@isnad1 id=iff.0h4v.s5.c8dec72f1e12 from=translated src=- shape=c8a4d81f vocab=a049915e
-/
@[simp]
theorem mem_offDiagonalNonsmoothSet {x h y n : ℕ} :
    n ∈ offDiagonalNonsmoothSet x h y ↔
      n ∈ nonsmoothShiftedSet x h y ∧ n ∉ aboveCutoffDiagonalSet x h y := by
  classical
  simp [offDiagonalNonsmoothSet]

/-- Fully expanded membership API for the off-diagonal remainder.
@isnad1 id=iff.0h4v.s6.6380d1cd2cf8 from=translated src=- shape=622e31a8 vocab=044bd6de
-/
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

/-- Proposition 9.7's first assertion: the displayed diagonal is contained in the nonsmooth shifted set.
@isnad1 id=le.0h3v.s4.434b2ce1c5fe from=translated src=- shape=99c9ad0c vocab=7dd608f0
-/
theorem diagonalSet_subset_nonsmoothShiftedSet (x h y : ℕ) :
    aboveCutoffDiagonalSet x h y ⊆ nonsmoothShiftedSet x h y :=
  aboveCutoffDiagonalSet_subset_nonsmoothShiftedSet x h y

/-- The off-diagonal remainder is contained in the nonsmooth shifted set.
@isnad1 id=le.0h3v.s4.745c992de76e from=translated src=- shape=99c9ad0c vocab=1c1611fc
-/
theorem offDiagonalNonsmoothSet_subset_nonsmoothShiftedSet (x h y : ℕ) :
    offDiagonalNonsmoothSet x h y ⊆ nonsmoothShiftedSet x h y := by
  exact Finset.sdiff_subset

/-- The diagonal and the off-diagonal remainder are disjoint.
@isnad1 id=disjoint.0h3v.s4.6147e1c22df3 from=translated src=- shape=99c9ad0c vocab=a81efbcf
-/
theorem aboveCutoffDiagonalSet_disjoint_offDiagonalNonsmoothSet (x h y : ℕ) :
    Disjoint (aboveCutoffDiagonalSet x h y) (offDiagonalNonsmoothSet x h y) := by
  exact Finset.disjoint_sdiff

/-- Exact set partition underlying Proposition 9.7.
@isnad1 id=eq.0h3v.s4.b1ac6c6861b9 from=translated src=- shape=9a3bb2ae vocab=276ee936
-/
theorem aboveCutoffDiagonalSet_union_offDiagonalNonsmoothSet (x h y : ℕ) :
    aboveCutoffDiagonalSet x h y ∪ offDiagonalNonsmoothSet x h y =
      nonsmoothShiftedSet x h y := by
  exact Finset.union_sdiff_of_subset (diagonalSet_subset_nonsmoothShiftedSet x h y)

/-- Exact cardinality identity `B_h = D_h + E_h`.
@isnad1 id=eq.0h3v.s4.3cebdad5a919 from=translated src=- shape=589a2fd4 vocab=f4d176a4
-/
theorem nonsmoothShiftedCount_eq_aboveCutoffDiagonalCount_add_offDiagonalNonsmoothCount
    (x h y : ℕ) :
    nonsmoothShiftedCount x h y =
      aboveCutoffDiagonalCount x h y + offDiagonalNonsmoothCount x h y := by
  rw [nonsmoothShiftedCount,
    ← aboveCutoffDiagonalSet_union_offDiagonalNonsmoothSet x h y,
    Finset.card_union_of_disjoint
      (aboveCutoffDiagonalSet_disjoint_offDiagonalNonsmoothSet x h y),
    aboveCutoffDiagonalCount, offDiagonalNonsmoothCount]

/-- Difference form of the exact identity: `B_h - D_h = E_h`.
@isnad1 id=eq.0h3v.s4.1287c804f017 from=translated src=- shape=61966b6b vocab=4d6d3ff6
-/
theorem nonsmoothShiftedCount_sub_aboveCutoffDiagonalCount (x h y : ℕ) :
    nonsmoothShiftedCount x h y - aboveCutoffDiagonalCount x h y =
      offDiagonalNonsmoothCount x h y := by
  rw [nonsmoothShiftedCount, aboveCutoffDiagonalCount, offDiagonalNonsmoothCount,
    offDiagonalNonsmoothSet]
  exact (Finset.card_sdiff_of_subset
    (diagonalSet_subset_nonsmoothShiftedSet x h y)).symm

/-- Both inequalities in the finite form of (9.4), together with its exact difference identity.
@isnad1 id=and.0h3v.s5.d341aabae2f3 from=translated src=- shape=6a605a3a vocab=02b8ca84
-/
theorem offDiagonalNonsmooth_cardinality_equation (x h y : ℕ) :
    aboveCutoffDiagonalCount x h y ≤ nonsmoothShiftedCount x h y ∧
      0 ≤ nonsmoothShiftedCount x h y - aboveCutoffDiagonalCount x h y ∧
      nonsmoothShiftedCount x h y - aboveCutoffDiagonalCount x h y =
        offDiagonalNonsmoothCount x h y := by
  exact ⟨aboveCutoffDiagonalCount_le_nonsmoothShiftedCount x h y, Nat.zero_le _,
    nonsmoothShiftedCount_sub_aboveCutoffDiagonalCount x h y⟩

/-- The off-diagonal remainder never exceeds the full nonsmooth count.
@isnad1 id=le.0h3v.s4.9f044e2de25e from=translated src=- shape=54938c17 vocab=986d8459
-/
theorem offDiagonalNonsmoothCount_le_nonsmoothShiftedCount (x h y : ℕ) :
    offDiagonalNonsmoothCount x h y ≤ nonsmoothShiftedCount x h y := by
  exact Finset.card_le_card (offDiagonalNonsmoothSet_subset_nonsmoothShiftedSet x h y)

/-- For a positive cutoff, the off-diagonal remainder lies in rank at least one.
@isnad1 id=le.1h3v.s5.b34a24fcbda5 from=translated src=- shape=b3dd7745 vocab=05c8a830
-/
theorem offDiagonalNonsmoothSet_subset_atLeastRankShiftedSet_one
    {x h y : ℕ} (hy : 1 ≤ y) :
    offDiagonalNonsmoothSet x h y ⊆ atLeastRankShiftedSet x h y 1 := by
  rw [atLeastRankShiftedSet_one_eq_nonsmoothShiftedSet hy]
  exact offDiagonalNonsmoothSet_subset_nonsmoothShiftedSet x h y

/-- At a positive cutoff, Proposition 9.7 is equivalently a partition of the rank-at-least-one stratum into its diagonal and off-diagonal pieces.
@isnad1 id=eq.1h3v.s5.54b67a3f9fc4 from=translated src=- shape=73a7e3e1 vocab=cf17fa62
-/
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

/-- Cardinal rank-one form of the displayed-diagonal transfer identity.
@isnad1 id=eq.1h3v.s5.73a323d948ab from=translated src=- shape=6b6922e6 vocab=fe561416
-/
theorem atLeastRankShiftedCount_one_eq_aboveCutoffDiagonalCount_add_offDiagonal
    {x h y : ℕ} (hy : 1 ≤ y) :
    atLeastRankShiftedCount x h y 1 =
      aboveCutoffDiagonalCount x h y + offDiagonalNonsmoothCount x h y := by
  rw [atLeastRankShiftedCount_one_eq_nonsmoothShiftedCount hy,
    nonsmoothShiftedCount_eq_aboveCutoffDiagonalCount_add_offDiagonalNonsmoothCount]

/-- The off-diagonal count is bounded by the rank-at-least-one count.
@isnad1 id=le.1h3v.s5.8b27bd938d1f from=translated src=- shape=c4d06ac3 vocab=6a715b5b
-/
theorem offDiagonalNonsmoothCount_le_atLeastRankShiftedCount_one
    {x h y : ℕ} (hy : 1 ≤ y) :
    offDiagonalNonsmoothCount x h y ≤ atLeastRankShiftedCount x h y 1 := by
  exact Finset.card_le_card (offDiagonalNonsmoothSet_subset_atLeastRankShiftedSet_one hy)

/-! ## Converse diagonal parametrization inside the finite transfer -/

/-- Converse Proposition 9.4 in predicate form: a diagonal provider skeleton with prime parameter and an above-cutoff common totient is an above-cutoff diagonal integer.
@isnad1 id=isabovec.3h5v.s5.17917257fa1e from=translated src=- shape=3dbaec10 vocab=25a3e364
-/
theorem LargePrimeSkeleton.isAboveCutoffDiagonal_of_isDiagonal {h n p y : ℕ}
    (s : LargePrimeSkeleton h n p) (hp : p.Prime) (hdiag : s.IsDiagonal)
    (hcut : y < largestPrimeFactor n.totient) :
    IsAboveCutoffDiagonal h y n := by
  obtain ⟨r, hrepresentation⟩ := s.exists_diagonalRepresentation hp hdiag hcut
  exact ⟨s.m1, r, hrepresentation⟩

/-- A supplied diagonal skeleton representing a member of the nonsmooth cutoff set is captured by the finite above-cutoff diagonal set.
@isnad1 id=mem.3h6v.s5.164bb7a7b0e1 from=translated src=- shape=4f902cd5 vocab=24456ac9
-/
theorem LargePrimeSkeleton.mem_aboveCutoffDiagonalSet_of_isDiagonal
    {x h n p y : ℕ} (s : LargePrimeSkeleton h n p) (hp : p.Prime)
    (hdiag : s.IsDiagonal) (hnonsmooth : n ∈ nonsmoothShiftedSet x h y) :
    n ∈ aboveCutoffDiagonalSet x h y := by
  have hnData := mem_nonsmoothShiftedSet.mp hnonsmooth
  apply mem_aboveCutoffDiagonalSet.mpr
  exact ⟨hnData.1, hnData.2.1,
    s.isAboveCutoffDiagonal_of_isDiagonal hp hdiag hnData.2.2.2⟩

/-- Consequently, a diagonal skeleton can never represent a member of the off-diagonal remainder.
@isnad1 id=not.2h6v.s5.b70d9d4fcb59 from=translated src=- shape=23e8a8ed vocab=b4b83093
-/
theorem LargePrimeSkeleton.not_mem_offDiagonalNonsmoothSet_of_isDiagonal
    {x h n p y : ℕ} (s : LargePrimeSkeleton h n p) (hp : p.Prime)
    (hdiag : s.IsDiagonal) :
    n ∉ offDiagonalNonsmoothSet x h y := by
  intro hn
  have hnData := mem_offDiagonalNonsmoothSet.mp hn
  exact hnData.2 (s.mem_aboveCutoffDiagonalSet_of_isDiagonal hp hdiag hnData.1)

/-- Conversely, any prime-parameter skeleton representing an element of the finite remainder is genuinely off diagonal.
@isnad1 id=not.2h6v.s5.02bc94d790cb from=translated src=- shape=3eb4f7b8 vocab=b4b83093
-/
theorem LargePrimeSkeleton.not_isDiagonal_of_mem_offDiagonalNonsmoothSet
    {x h n p y : ℕ} (s : LargePrimeSkeleton h n p) (hp : p.Prime)
    (hn : n ∈ offDiagonalNonsmoothSet x h y) :
    ¬s.IsDiagonal := by
  intro hdiag
  exact s.not_mem_offDiagonalNonsmoothSet_of_isDiagonal hp hdiag hn

/-! ## Parity consequences -/

/-- An odd shift has no diagonal provider skeleton.
@isnad1 id=not.1h4v.s4.1cd625dbca48 from=translated src=- shape=b4d71ebd vocab=49cde9ba
-/
theorem LargePrimeSkeleton.not_isDiagonal_of_odd {h n p : ℕ} (hodd : Odd h)
    (s : LargePrimeSkeleton h n p) :
    ¬s.IsDiagonal := by
  simpa only [LargePrimeSkeleton.IsDiagonal] using s.normalized_slopes_ne hodd

/-- For odd shifts the off-diagonal remainder is the entire nonsmooth set.
@isnad1 id=eq.1h3v.s4.bd076507bcad from=translated src=- shape=d8d1abc6 vocab=4847a69a
-/
theorem offDiagonalNonsmoothSet_eq_nonsmoothShiftedSet_of_odd
    {x h y : ℕ} (hodd : Odd h) :
    offDiagonalNonsmoothSet x h y = nonsmoothShiftedSet x h y := by
  rw [offDiagonalNonsmoothSet, aboveCutoffDiagonalSet_eq_empty_of_odd hodd]
  exact Finset.sdiff_empty

/-- Count form of the odd-shift collapse of the diagonal decomposition.
@isnad1 id=eq.1h3v.s4.417b818ac7a6 from=translated src=- shape=0f5ac81f vocab=d04bd664
-/
theorem offDiagonalNonsmoothCount_eq_nonsmoothShiftedCount_of_odd
    {x h y : ℕ} (hodd : Odd h) :
    offDiagonalNonsmoothCount x h y = nonsmoothShiftedCount x h y := by
  rw [offDiagonalNonsmoothCount,
    offDiagonalNonsmoothSet_eq_nonsmoothShiftedSet_of_odd hodd,
    nonsmoothShiftedCount]

end RankAmplification
