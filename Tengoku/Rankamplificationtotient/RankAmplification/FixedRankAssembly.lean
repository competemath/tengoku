import Tengoku.Rankamplificationtotient.RankAmplification.FixedRankScales
import Tengoku.Rankamplificationtotient.RankAmplification.DiagonalTransfer
import Tengoku.Rankamplificationtotient.RankAmplification.RankStrata

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Exact fixed-rank assembly The proof of Theorem 10.13 splits every shifted equal-totient solution according to two tests on its common totient: whether its largest prime factor exceeds the upper cutoff `Y`, and whether its number of prime-factor occurrences above the lower cutoff `y` reaches the fixed rank `J`. -/

namespace RankAmplification

noncomputable section

/-! ## The bounded-value rank split -/

/-- Bounded common totient and rank below `J`.-/
def fixedLowRankShiftedSet (x h y Y J : ℕ) : Finset ℕ :=
  (shiftedEqualTotientSet x h).filter fun n ↦
    largestPrimeFactor n.totient ≤ Y ∧ largePrimeRank y n.totient < J

/-- Cardinality of the bounded common-totient branch below rank `J`.-/
def fixedLowRankShiftedCount (x h y Y J : ℕ) : ℕ :=
  (fixedLowRankShiftedSet x h y Y J).card

/-- Bounded common totient and rank at least `J`.-/
def fixedHighRankShiftedSet (x h y Y J : ℕ) : Finset ℕ :=
  (shiftedEqualTotientSet x h).filter fun n ↦
    largestPrimeFactor n.totient ≤ Y ∧ J ≤ largePrimeRank y n.totient

/-- Cardinality of the bounded common-totient branch at rank at least `J`.-/
def fixedHighRankShiftedCount (x h y Y J : ℕ) : ℕ :=
  (fixedHighRankShiftedSet x h y Y J).card

/-- The common-totient values whose largest prime factor is at most `Y`.-/
def fixedBoundedValueShiftedSet (x h Y : ℕ) : Finset ℕ :=
  (shiftedEqualTotientSet x h).filter fun n ↦
    largestPrimeFactor n.totient ≤ Y

/--
@isnad1 id=iff.0h6v.s5.5e254d69390b from=translated src=- shape=fad1048a vocab=aecaab15
-/
@[simp] theorem mem_fixedLowRankShiftedSet {x h y Y J n : ℕ} :
    n ∈ fixedLowRankShiftedSet x h y Y J ↔
      n ∈ shiftedEqualTotientSet x h ∧
        largestPrimeFactor n.totient ≤ Y ∧ largePrimeRank y n.totient < J := by
  simp [fixedLowRankShiftedSet]

/--
@isnad1 id=iff.0h6v.s5.b6003f9064ed from=translated src=- shape=7694d2bb vocab=f9a6e00e
-/
@[simp] theorem mem_fixedHighRankShiftedSet {x h y Y J n : ℕ} :
    n ∈ fixedHighRankShiftedSet x h y Y J ↔
      n ∈ shiftedEqualTotientSet x h ∧
        largestPrimeFactor n.totient ≤ Y ∧ J ≤ largePrimeRank y n.totient := by
  simp [fixedHighRankShiftedSet]

/--
@isnad1 id=iff.0h4v.s5.b4f551b757c9 from=translated src=- shape=b67defbd vocab=4f5aa9da
-/
@[simp] theorem mem_fixedBoundedValueShiftedSet {x h Y n : ℕ} :
    n ∈ fixedBoundedValueShiftedSet x h Y ↔
      n ∈ shiftedEqualTotientSet x h ∧
        largestPrimeFactor n.totient ≤ Y := by
  simp [fixedBoundedValueShiftedSet]

/--
@isnad1 id=le.0h5v.s5.df30af2422cc from=translated src=- shape=0dab571d vocab=8a82351f
-/
theorem fixedLowRankShiftedSet_subset_belowRank
    (x h y Y J : ℕ) :
    fixedLowRankShiftedSet x h y Y J ⊆ belowRankShiftedSet x h y J := by
  intro n hn
  exact mem_belowRankShiftedSet.mpr
    ⟨(mem_fixedLowRankShiftedSet.mp hn).1,
      (mem_fixedLowRankShiftedSet.mp hn).2.2⟩

/--
@isnad1 id=le.0h5v.s5.b2ed6a2c5cb0 from=translated src=- shape=0dab571d vocab=5532aae8
-/
theorem fixedHighRankShiftedSet_subset_atLeastRank
    (x h y Y J : ℕ) :
    fixedHighRankShiftedSet x h y Y J ⊆ atLeastRankShiftedSet x h y J := by
  intro n hn
  exact mem_atLeastRankShiftedSet.mpr
    ⟨(mem_fixedHighRankShiftedSet.mp hn).1,
      (mem_fixedHighRankShiftedSet.mp hn).2.2⟩

/--
@isnad1 id=le.0h5v.s4.f87ed347072a from=translated src=- shape=94167779 vocab=ae146801
-/
theorem fixedLowRankShiftedCount_le_belowRankCard (x h y Y J : ℕ) :
    fixedLowRankShiftedCount x h y Y J ≤
      (belowRankShiftedSet x h y J).card :=
  Finset.card_le_card (fixedLowRankShiftedSet_subset_belowRank x h y Y J)

/--
@isnad1 id=le.0h5v.s4.0e45417a0e72 from=translated src=- shape=c5b1e91d vocab=9a215ce3
-/
theorem fixedHighRankShiftedCount_le_atLeastRankCount (x h y Y J : ℕ) :
    fixedHighRankShiftedCount x h y Y J ≤
      atLeastRankShiftedCount x h y J := by
  exact Finset.card_le_card (fixedHighRankShiftedSet_subset_atLeastRank x h y Y J)

/-- The rank alternatives partition the bounded-value branch.
@isnad1 id=eq.0h5v.s5.3ec34beda9d6 from=translated src=- shape=e3f7e5ea vocab=fe4900fb
-/
theorem fixedLowRank_union_highRank (x h y Y J : ℕ) :
    fixedLowRankShiftedSet x h y Y J ∪ fixedHighRankShiftedSet x h y Y J =
      fixedBoundedValueShiftedSet x h Y := by
  ext n
  simp only [Finset.mem_union, mem_fixedLowRankShiftedSet,
    mem_fixedHighRankShiftedSet, mem_fixedBoundedValueShiftedSet]
  constructor
  · rintro (⟨hn, hY, _⟩ | ⟨hn, hY, _⟩)
    · exact ⟨hn, hY⟩
    · exact ⟨hn, hY⟩
  · rintro ⟨hn, hY⟩
    rcases lt_or_ge (largePrimeRank y n.totient) J with hr | hr
    · exact Or.inl ⟨hn, hY, hr⟩
    · exact Or.inr ⟨hn, hY, hr⟩

/--
@isnad1 id=disjoint.0h5v.s4.0a7d41d71f1b from=translated src=- shape=50e38918 vocab=1ffccf46
-/
theorem fixedLowRank_disjoint_highRank (x h y Y J : ℕ) :
    Disjoint (fixedLowRankShiftedSet x h y Y J)
      (fixedHighRankShiftedSet x h y Y J) := by
  rw [Finset.disjoint_left]
  intro n hnlow hnhigh
  have hl := (mem_fixedLowRankShiftedSet.mp hnlow).2.2
  have hh := (mem_fixedHighRankShiftedSet.mp hnhigh).2.2
  omega

/--
@isnad1 id=eq.0h5v.s5.a23cb77c1ef3 from=translated src=- shape=90a39bec vocab=9919c0be
-/
theorem fixedBoundedValueCount_eq_low_add_high (x h y Y J : ℕ) :
    (fixedBoundedValueShiftedSet x h Y).card =
      fixedLowRankShiftedCount x h y Y J +
        fixedHighRankShiftedCount x h y Y J := by
  rw [← fixedLowRank_union_highRank x h y Y J,
    Finset.card_union_of_disjoint (fixedLowRank_disjoint_highRank x h y Y J)]
  rfl

/-! ## The largest-prime-factor split -/

/--
@isnad1 id=disjoint.0h3v.s4.63d772614581 from=translated src=- shape=99c9ad0c vocab=bacb84cc
-/
theorem fixedBoundedValue_disjoint_nonsmooth (x h Y : ℕ) :
    Disjoint (fixedBoundedValueShiftedSet x h Y)
      (nonsmoothShiftedSet x h Y) := by
  rw [Finset.disjoint_left]
  intro n hbounded hnonsmooth
  have hb := mem_fixedBoundedValueShiftedSet.mp hbounded
  have hn := mem_nonsmoothShiftedSet.mp hnonsmooth
  omega

/--
@isnad1 id=eq.0h3v.s4.b5feac407678 from=translated src=- shape=4f04af0a vocab=a25b640b
-/
theorem fixedBoundedValue_union_nonsmooth (x h Y : ℕ) :
    fixedBoundedValueShiftedSet x h Y ∪ nonsmoothShiftedSet x h Y =
      shiftedEqualTotientSet x h := by
  ext n
  simp only [Finset.mem_union, mem_fixedBoundedValueShiftedSet,
    mem_nonsmoothShiftedSet]
  constructor
  · rintro (hn | hn)
    · exact hn.1
    · exact mem_shiftedEqualTotientSet.mpr ⟨hn.1, hn.2.1, hn.2.2.1⟩
  · intro hn
    by_cases hle : largestPrimeFactor n.totient ≤ Y
    · exact Or.inl ⟨hn, hle⟩
    · have hndata := mem_shiftedEqualTotientSet.mp hn
      exact Or.inr ⟨hndata.1, hndata.2.1, hndata.2.2,
        Nat.lt_of_not_ge hle⟩

/-- Exact four-way cardinality identity underlying Theorem 10.13.
@isnad1 id=eq.0h5v.s5.2e7ca45c86cd from=translated src=- shape=eadec35e vocab=376ca763
-/
theorem fixedRank_exact_diagonal_decomposition (x h y Y J : ℕ) :
    shiftedEqualTotientCount x h =
      aboveCutoffDiagonalCount x h Y + offDiagonalNonsmoothCount x h Y +
        fixedLowRankShiftedCount x h y Y J +
          fixedHighRankShiftedCount x h y Y J := by
  have htotal : shiftedEqualTotientCount x h =
      (fixedBoundedValueShiftedSet x h Y).card +
        nonsmoothShiftedCount x h Y := by
    rw [shiftedEqualTotientCount, ← fixedBoundedValue_union_nonsmooth x h Y,
      Finset.card_union_of_disjoint
        (fixedBoundedValue_disjoint_nonsmooth x h Y),
      nonsmoothShiftedCount]
  rw [fixedBoundedValueCount_eq_low_add_high x h y Y J,
    nonsmoothShiftedCount_eq_aboveCutoffDiagonalCount_add_offDiagonalNonsmoothCount
      x h Y] at htotal
  omega

/-- Set-level version of the same four disjoint branches.
@isnad1 id=eq.0h5v.s5.3700362995be from=translated src=- shape=523fb04e vocab=75fb2d53
-/
theorem fixedRank_fourBranch_union (x h y Y J : ℕ) :
    aboveCutoffDiagonalSet x h Y ∪ offDiagonalNonsmoothSet x h Y ∪
        fixedLowRankShiftedSet x h y Y J ∪
          fixedHighRankShiftedSet x h y Y J =
      shiftedEqualTotientSet x h := by
  calc
    aboveCutoffDiagonalSet x h Y ∪ offDiagonalNonsmoothSet x h Y ∪
          fixedLowRankShiftedSet x h y Y J ∪
            fixedHighRankShiftedSet x h y Y J =
        (aboveCutoffDiagonalSet x h Y ∪ offDiagonalNonsmoothSet x h Y) ∪
          (fixedLowRankShiftedSet x h y Y J ∪
            fixedHighRankShiftedSet x h y Y J) := by
      simp only [Finset.union_assoc]
    _ = nonsmoothShiftedSet x h Y ∪ fixedBoundedValueShiftedSet x h Y := by
      rw [aboveCutoffDiagonalSet_union_offDiagonalNonsmoothSet,
        fixedLowRank_union_highRank]
    _ = fixedBoundedValueShiftedSet x h Y ∪ nonsmoothShiftedSet x h Y := by
      rw [Finset.union_comm]
    _ = shiftedEqualTotientSet x h := fixedBoundedValue_union_nonsmooth x h Y

/-! ## Pointwise assembly of branch estimates -/

/-- Separate real upper bounds for the three off-diagonal branches.-/
structure FixedRankBranchBounds
    (x h y Y J : ℕ) (low high off : ℝ) : Prop where
  low_bound : (fixedLowRankShiftedCount x h y Y J : ℝ) ≤ low
  high_bound : (fixedHighRankShiftedCount x h y Y J : ℝ) ≤ high
  off_bound : (offDiagonalNonsmoothCount x h Y : ℝ) ≤ off

/-- The exact decomposition plus three supplied pointwise estimates.
@isnad1 id=le.1h8v.s6.e4e9b079df24 from=translated src=- shape=5815cb51 vocab=5247116f
-/
theorem fixedRank_count_le_diagonal_add_branches
    {x h y Y J : ℕ} {low high off : ℝ}
    (bounds : FixedRankBranchBounds x h y Y J low high off) :
    (shiftedEqualTotientCount x h : ℝ) ≤
      (aboveCutoffDiagonalCount x h Y : ℝ) + off + low + high := by
  have hexact : (shiftedEqualTotientCount x h : ℝ) =
      (aboveCutoffDiagonalCount x h Y : ℝ) +
        offDiagonalNonsmoothCount x h Y +
        fixedLowRankShiftedCount x h y Y J +
        fixedHighRankShiftedCount x h y Y J := by
    exact_mod_cast fixedRank_exact_diagonal_decomposition x h y Y J
  rw [hexact]
  linarith [bounds.off_bound, bounds.low_bound, bounds.high_bound]

/-- If all three branches have the same majorant, their total costs at most three copies.
@isnad1 id=le.3h6v.s6.6e3607038968 from=translated src=- shape=3e4d3233 vocab=e0276fce
-/
theorem fixedRank_count_le_diagonal_add_three_mul
    {x h y Y J : ℕ} {error : ℝ}
    (hlow : (fixedLowRankShiftedCount x h y Y J : ℝ) ≤ error)
    (hhigh : (fixedHighRankShiftedCount x h y Y J : ℝ) ≤ error)
    (hoff : (offDiagonalNonsmoothCount x h Y : ℝ) ≤ error) :
    (shiftedEqualTotientCount x h : ℝ) ≤
      (aboveCutoffDiagonalCount x h Y : ℝ) + 3 * error := by
  have hmain := fixedRank_count_le_diagonal_add_branches
    (FixedRankBranchBounds.mk hlow hhigh hoff)
  linarith

/-- Odd shifts have no displayed diagonal.
@isnad1 id=le.2h8v.s5.896d93910a8b from=translated src=- shape=26938188 vocab=defc28d1
-/
theorem fixedRank_odd_count_le_branches
    {x h y Y J : ℕ} {low high off : ℝ} (hodd : Odd h)
    (bounds : FixedRankBranchBounds x h y Y J low high off) :
    (shiftedEqualTotientCount x h : ℝ) ≤ off + low + high := by
  simpa [aboveCutoffDiagonalCount_eq_zero_of_odd hodd] using
    fixedRank_count_le_diagonal_add_branches bounds

/--
@isnad1 id=le.4h6v.s6.605dc52064ca from=translated src=- shape=b9e2e38a vocab=79c042ee
-/
theorem fixedRank_odd_count_le_three_mul
    {x h y Y J : ℕ} {error : ℝ} (hodd : Odd h)
    (hlow : (fixedLowRankShiftedCount x h y Y J : ℝ) ≤ error)
    (hhigh : (fixedHighRankShiftedCount x h y Y J : ℝ) ≤ error)
    (hoff : (offDiagonalNonsmoothCount x h Y : ℝ) ≤ error) :
    (shiftedEqualTotientCount x h : ℝ) ≤ 3 * error := by
  simpa [aboveCutoffDiagonalCount_eq_zero_of_odd hodd] using
    fixedRank_count_le_diagonal_add_three_mul hlow hhigh hoff

/-! ## Specialization to the paper's natural fixed-rank cutoffs -/

/-- Fixed low-rank count at the optimized natural cutoffs of Theorem 10.14.-/
def paperFixedLowRankShiftedCount (J x h : ℕ) : ℕ :=
  fixedLowRankShiftedCount x h (fixedRankNatY J x)
    (fixedRankNatUpperY J x) J

/-- Fixed high-rank count at the optimized natural cutoffs of Theorem 10.14.-/
def paperFixedHighRankShiftedCount (J x h : ℕ) : ℕ :=
  fixedHighRankShiftedCount x h (fixedRankNatY J x)
    (fixedRankNatUpperY J x) J

/--
@isnad1 id=eq.0h3v.s5.9fcce90e5b23 from=translated src=- shape=3b8de94b vocab=16ee0524
-/
theorem paperFixedRank_exact_diagonal_decomposition (J x h : ℕ) :
    shiftedEqualTotientCount x h =
      aboveCutoffDiagonalCount x h (fixedRankNatUpperY J x) +
        offDiagonalNonsmoothCount x h (fixedRankNatUpperY J x) +
        paperFixedLowRankShiftedCount J x h +
        paperFixedHighRankShiftedCount J x h := by
  exact fixedRank_exact_diagonal_decomposition x h
    (fixedRankNatY J x) (fixedRankNatUpperY J x) J

end

end RankAmplification
