import Tengoku.Rankamplificationtotient.RankAmplification.Counting
import Tengoku.Rankamplificationtotient.RankAmplification.Elementary

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Finite chains of equal totients This module formalizes the exact set-theoretic content of Section 11. -/

namespace RankAmplification

/-- The values at `n, n + h, ..., n + (r - 1)h` all have the same totient.-/
def IsTotientChain (r h n : ℕ) : Prop :=
  ∀ k < r, n.totient = (n + k * h).totient

/-- The finite set underlying the paper's chain count `C^φ_{r,h}(x)`.-/
noncomputable def totientChainSet (x r h : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 x).filter fun n ↦ IsTotientChain r h n

/-- The exact chain counting function `C^φ_{r,h}(x)`.-/
noncomputable def totientChainCount (x r h : ℕ) : ℕ :=
  (totientChainSet x r h).card

/-- Chain integers whose first pair lies in the above-cutoff diagonal.-/
noncomputable def firstPairDiagonalChainSet (x r h Y : ℕ) : Finset ℕ :=
  totientChainSet x r h ∩ aboveCutoffDiagonalSet x h Y

/-- The exact first-pair diagonal chain count `D^φ_{r,h,>Y}(x)`.-/
noncomputable def firstPairDiagonalChainCount (x r h Y : ℕ) : ℕ :=
  (firstPairDiagonalChainSet x r h Y).card

@[simp]
theorem mem_totientChainSet {x r h n : ℕ} :
    n ∈ totientChainSet x r h ↔ 1 ≤ n ∧ n ≤ x ∧ IsTotientChain r h n := by
  classical
  simp [totientChainSet, and_assoc]

@[simp]
theorem mem_firstPairDiagonalChainSet {x r h Y n : ℕ} :
    n ∈ firstPairDiagonalChainSet x r h Y ↔
      n ∈ totientChainSet x r h ∧ n ∈ aboveCutoffDiagonalSet x h Y := by
  classical
  simp [firstPairDiagonalChainSet]

/-- A chain of length at least two contains its first shifted pair.-/
theorem IsTotientChain.firstPair {r h n : ℕ} (hchain : IsTotientChain r h n)
    (hr : 2 ≤ r) :
    n.totient = (n + h).totient := by
  simpa using hchain 1 (by omega)

/-- The first inequality in (11.1) at the level of finite sets.-/
theorem firstPairDiagonalChainSet_subset_aboveCutoffDiagonalSet (x r h Y : ℕ) :
    firstPairDiagonalChainSet x r h Y ⊆ aboveCutoffDiagonalSet x h Y := by
  classical
  exact Finset.inter_subset_right

/-- The first-pair diagonal chain set is also a subset of the full chain set.-/
theorem firstPairDiagonalChainSet_subset_totientChainSet (x r h Y : ℕ) :
    firstPairDiagonalChainSet x r h Y ⊆ totientChainSet x r h := by
  classical
  exact Finset.inter_subset_left

/-- A chain of length at least two is a shifted equal-totient solution.-/
theorem totientChainSet_subset_shiftedEqualTotientSet {x r h : ℕ} (hr : 2 ≤ r) :
    totientChainSet x r h ⊆ shiftedEqualTotientSet x h := by
  intro n hn
  rw [mem_totientChainSet] at hn
  rw [mem_shiftedEqualTotientSet]
  exact ⟨hn.1, hn.2.1, hn.2.2.firstPair hr⟩

/-- The diagonal-chain cardinality inequality in (11.1).-/
theorem firstPairDiagonalChainCount_le_aboveCutoffDiagonalCount (x r h Y : ℕ) :
    firstPairDiagonalChainCount x r h Y ≤ aboveCutoffDiagonalCount x h Y := by
  exact Finset.card_le_card
    (firstPairDiagonalChainSet_subset_aboveCutoffDiagonalSet x r h Y)

/-- The first-pair diagonal chain count is also bounded by the whole chain count.-/
theorem firstPairDiagonalChainCount_le_totientChainCount (x r h Y : ℕ) :
    firstPairDiagonalChainCount x r h Y ≤ totientChainCount x r h := by
  exact Finset.card_le_card (firstPairDiagonalChainSet_subset_totientChainSet x r h Y)

/-- The pair-count cardinality inequality in (11.1).-/
theorem totientChainCount_le_shiftedEqualTotientCount {x r h : ℕ} (hr : 2 ≤ r) :
    totientChainCount x r h ≤ shiftedEqualTotientCount x h := by
  exact Finset.card_le_card (totientChainSet_subset_shiftedEqualTotientSet hr)

/-- The three cardinality comparisons displayed in (11.1), including the natural-number lower bound.-/
theorem chain_cardinality_equation_11_1 {x r h Y : ℕ} (hr : 2 ≤ r) :
    0 ≤ firstPairDiagonalChainCount x r h Y ∧
      firstPairDiagonalChainCount x r h Y ≤ aboveCutoffDiagonalCount x h Y ∧
      totientChainCount x r h ≤ shiftedEqualTotientCount x h :=
  ⟨Nat.zero_le _, firstPairDiagonalChainCount_le_aboveCutoffDiagonalCount x r h Y,
    totientChainCount_le_shiftedEqualTotientCount hr⟩

/-- The pair diagonal is contained in the pair solution set.-/
theorem aboveCutoffDiagonalSet_subset_shiftedEqualTotientSet (x h Y : ℕ) :
    aboveCutoffDiagonalSet x h Y ⊆ shiftedEqualTotientSet x h :=
  (aboveCutoffDiagonalSet_subset_nonsmoothShiftedSet x h Y).trans
    (nonsmoothShiftedSet_subset x h Y)

/-- Removing the first-pair diagonal from the chain leaves a subset of the pair off-diagonal set.-/
theorem chain_sdiff_diagonal_subset_pair_sdiff_diagonal {x r h Y : ℕ} (hr : 2 ≤ r) :
    totientChainSet x r h \ aboveCutoffDiagonalSet x h Y ⊆
      shiftedEqualTotientSet x h \ aboveCutoffDiagonalSet x h Y := by
  exact Finset.sdiff_subset_sdiff_left (aboveCutoffDiagonalSet x h Y)
    (totientChainSet_subset_shiftedEqualTotientSet hr)

/-- The chain off-diagonal cardinality is exactly subtraction of its diagonal count.-/
theorem totientChainCount_sub_firstPairDiagonalChainCount (x r h Y : ℕ) :
    totientChainCount x r h - firstPairDiagonalChainCount x r h Y =
      (totientChainSet x r h \ aboveCutoffDiagonalSet x h Y).card := by
  classical
  rw [totientChainCount, firstPairDiagonalChainCount, firstPairDiagonalChainSet]
  rw [← Finset.card_sdiff_of_subset Finset.inter_subset_left]
  congr 1
  ext n
  simp

/-- The pair off-diagonal cardinality is likewise an exact subtraction.-/
theorem shiftedEqualTotientCount_sub_aboveCutoffDiagonalCount (x h Y : ℕ) :
    shiftedEqualTotientCount x h - aboveCutoffDiagonalCount x h Y =
      (shiftedEqualTotientSet x h \ aboveCutoffDiagonalSet x h Y).card := by
  rw [shiftedEqualTotientCount, aboveCutoffDiagonalCount]
  exact (Finset.card_sdiff_of_subset
    (aboveCutoffDiagonalSet_subset_shiftedEqualTotientSet x h Y)).symm

/-- The exact finite cardinality inequality used in the proof of Corollary 11.1.-/
theorem chain_offDiagonal_cardinality_le_pair_offDiagonal_cardinality {x r h Y : ℕ}
    (hr : 2 ≤ r) :
    totientChainCount x r h - firstPairDiagonalChainCount x r h Y ≤
      shiftedEqualTotientCount x h - aboveCutoffDiagonalCount x h Y := by
  rw [totientChainCount_sub_firstPairDiagonalChainCount,
    shiftedEqualTotientCount_sub_aboveCutoffDiagonalCount]
  exact Finset.card_le_card (chain_sdiff_diagonal_subset_pair_sdiff_diagonal hr)

/-- Both inequalities displayed in the set-theoretic proof of Corollary 11.1.-/
theorem chain_offDiagonal_cardinality_bounds {x r h Y : ℕ} (hr : 2 ≤ r) :
    0 ≤ totientChainCount x r h - firstPairDiagonalChainCount x r h Y ∧
      totientChainCount x r h - firstPairDiagonalChainCount x r h Y ≤
        shiftedEqualTotientCount x h - aboveCutoffDiagonalCount x h Y :=
  ⟨Nat.zero_le _, chain_offDiagonal_cardinality_le_pair_offDiagonal_cardinality hr⟩

/-- Odd shifts have no first-pair diagonal chain integers.-/
theorem firstPairDiagonalChainSet_eq_empty_of_odd {x r h Y : ℕ} (hodd : Odd h) :
    firstPairDiagonalChainSet x r h Y = ∅ := by
  classical
  rw [firstPairDiagonalChainSet, aboveCutoffDiagonalSet_eq_empty_of_odd hodd]
  exact Finset.inter_empty _

/-- Thus the first-pair diagonal chain count vanishes for odd shifts.-/
theorem firstPairDiagonalChainCount_eq_zero_of_odd {x r h Y : ℕ} (hodd : Odd h) :
    firstPairDiagonalChainCount x r h Y = 0 := by
  rw [firstPairDiagonalChainCount, firstPairDiagonalChainSet_eq_empty_of_odd hodd]
  rfl

/-- A chain of length two is exactly one shifted equal-totient equation.-/
@[simp]
theorem isTotientChain_two (h n : ℕ) :
    IsTotientChain 2 h n ↔ n.totient = (n + h).totient := by
  constructor
  · intro hchain
    exact hchain.firstPair (by omega)
  · intro heq k hk
    have hkcases : k = 0 ∨ k = 1 := by omega
    rcases hkcases with rfl | rfl
    · simp
    · simpa using heq

/-- The length-two chain set is the shifted equal-totient set.-/
@[simp]
theorem totientChainSet_two (x h : ℕ) :
    totientChainSet x 2 h = shiftedEqualTotientSet x h := by
  classical
  ext n
  simp

/-- The length-two chain count is the shifted equal-totient count.-/
@[simp]
theorem totientChainCount_two (x h : ℕ) :
    totientChainCount x 2 h = shiftedEqualTotientCount x h := by
  rw [totientChainCount, shiftedEqualTotientCount, totientChainSet_two]

/-- At length two, the first-pair chain diagonal is the full pair diagonal.-/
@[simp]
theorem firstPairDiagonalChainSet_two (x h Y : ℕ) :
    firstPairDiagonalChainSet x 2 h Y = aboveCutoffDiagonalSet x h Y := by
  classical
  rw [firstPairDiagonalChainSet, totientChainSet_two]
  exact Finset.inter_eq_right.mpr
    (aboveCutoffDiagonalSet_subset_shiftedEqualTotientSet x h Y)

/-- The corresponding length-two diagonal counts agree.-/
@[simp]
theorem firstPairDiagonalChainCount_two (x h Y : ℕ) :
    firstPairDiagonalChainCount x 2 h Y = aboveCutoffDiagonalCount x h Y := by
  rw [firstPairDiagonalChainCount, aboveCutoffDiagonalCount,
    firstPairDiagonalChainSet_two]

/-- At length two, the chain and pair off-diagonal cardinalities are identical.-/
@[simp, nolint simpNF]
theorem chain_offDiagonal_cardinality_two (x h Y : ℕ) :
    totientChainCount x 2 h - firstPairDiagonalChainCount x 2 h Y =
      shiftedEqualTotientCount x h - aboveCutoffDiagonalCount x h Y := by
  rw [totientChainCount_two, firstPairDiagonalChainCount_two]

end RankAmplification
