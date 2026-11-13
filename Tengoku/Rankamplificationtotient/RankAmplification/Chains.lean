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

/--
@isnad1 id=iff.0h4v.s5.dda0c9003424 from=translated src=- shape=dede7a53 vocab=33e48f98
-/
@[simp]
theorem mem_totientChainSet {x r h n : ℕ} :
    n ∈ totientChainSet x r h ↔ 1 ≤ n ∧ n ≤ x ∧ IsTotientChain r h n := by
  classical
  simp [totientChainSet, and_assoc]

/--
@isnad1 id=iff.0h5v.s5.0947484eb0d2 from=translated src=- shape=4b05cf00 vocab=a804484b
-/
@[simp]
theorem mem_firstPairDiagonalChainSet {x r h Y n : ℕ} :
    n ∈ firstPairDiagonalChainSet x r h Y ↔
      n ∈ totientChainSet x r h ∧ n ∈ aboveCutoffDiagonalSet x h Y := by
  classical
  simp [firstPairDiagonalChainSet]

/-- A chain of length at least two contains its first shifted pair.
@isnad1 id=eq.2h3v.s5.32edeb50ea1b from=translated src=- shape=92a59c4a vocab=9dd7c72d
-/
theorem IsTotientChain.firstPair {r h n : ℕ} (hchain : IsTotientChain r h n)
    (hr : 2 ≤ r) :
    n.totient = (n + h).totient := by
  simpa using hchain 1 (by omega)

/-- The first inequality in (11.1) at the level of finite sets.
@isnad1 id=le.0h4v.s4.2a53a9875811 from=translated src=- shape=a553ca17 vocab=27341e54
-/
theorem firstPairDiagonalChainSet_subset_aboveCutoffDiagonalSet (x r h Y : ℕ) :
    firstPairDiagonalChainSet x r h Y ⊆ aboveCutoffDiagonalSet x h Y := by
  classical
  exact Finset.inter_subset_right

/-- The first-pair diagonal chain set is also a subset of the full chain set.
@isnad1 id=le.0h4v.s4.7a6b68f448e7 from=translated src=- shape=3c2f1259 vocab=fe73dacc
-/
theorem firstPairDiagonalChainSet_subset_totientChainSet (x r h Y : ℕ) :
    firstPairDiagonalChainSet x r h Y ⊆ totientChainSet x r h := by
  classical
  exact Finset.inter_subset_left

/-- A chain of length at least two is a shifted equal-totient solution.
@isnad1 id=le.1h3v.s5.222f686c0446 from=translated src=- shape=337f3de2 vocab=536410a6
-/
theorem totientChainSet_subset_shiftedEqualTotientSet {x r h : ℕ} (hr : 2 ≤ r) :
    totientChainSet x r h ⊆ shiftedEqualTotientSet x h := by
  intro n hn
  rw [mem_totientChainSet] at hn
  rw [mem_shiftedEqualTotientSet]
  exact ⟨hn.1, hn.2.1, hn.2.2.firstPair hr⟩

/-- The diagonal-chain cardinality inequality in (11.1).
@isnad1 id=le.0h4v.s4.00620258ad10 from=translated src=- shape=a457f8d2 vocab=b2cbc2cc
-/
theorem firstPairDiagonalChainCount_le_aboveCutoffDiagonalCount (x r h Y : ℕ) :
    firstPairDiagonalChainCount x r h Y ≤ aboveCutoffDiagonalCount x h Y := by
  exact Finset.card_le_card
    (firstPairDiagonalChainSet_subset_aboveCutoffDiagonalSet x r h Y)

/-- The first-pair diagonal chain count is also bounded by the whole chain count.
@isnad1 id=le.0h4v.s4.75a1fdb5e1c3 from=translated src=- shape=cb492927 vocab=9e25b9a4
-/
theorem firstPairDiagonalChainCount_le_totientChainCount (x r h Y : ℕ) :
    firstPairDiagonalChainCount x r h Y ≤ totientChainCount x r h := by
  exact Finset.card_le_card (firstPairDiagonalChainSet_subset_totientChainSet x r h Y)

/-- The pair-count cardinality inequality in (11.1).
@isnad1 id=le.1h3v.s4.1a14e50292ad from=translated src=- shape=afa8d857 vocab=2253f073
-/
theorem totientChainCount_le_shiftedEqualTotientCount {x r h : ℕ} (hr : 2 ≤ r) :
    totientChainCount x r h ≤ shiftedEqualTotientCount x h := by
  exact Finset.card_le_card (totientChainSet_subset_shiftedEqualTotientSet hr)

/-- The three cardinality comparisons displayed in (11.1), including the natural-number lower bound.
@isnad1 id=and.1h4v.s5.3e09a693f0f3 from=translated src=- shape=373cf0f9 vocab=d3f24668
-/
theorem chain_cardinality_equation_11_1 {x r h Y : ℕ} (hr : 2 ≤ r) :
    0 ≤ firstPairDiagonalChainCount x r h Y ∧
      firstPairDiagonalChainCount x r h Y ≤ aboveCutoffDiagonalCount x h Y ∧
      totientChainCount x r h ≤ shiftedEqualTotientCount x h :=
  ⟨Nat.zero_le _, firstPairDiagonalChainCount_le_aboveCutoffDiagonalCount x r h Y,
    totientChainCount_le_shiftedEqualTotientCount hr⟩

/-- The pair diagonal is contained in the pair solution set.
@isnad1 id=le.0h3v.s4.c4b11d05cb70 from=translated src=- shape=202d3bc8 vocab=1e46e680
-/
theorem aboveCutoffDiagonalSet_subset_shiftedEqualTotientSet (x h Y : ℕ) :
    aboveCutoffDiagonalSet x h Y ⊆ shiftedEqualTotientSet x h :=
  (aboveCutoffDiagonalSet_subset_nonsmoothShiftedSet x h Y).trans
    (nonsmoothShiftedSet_subset x h Y)

/-- Removing the first-pair diagonal from the chain leaves a subset of the pair off-diagonal set.
@isnad1 id=le.1h4v.s5.58d69aeabd9f from=translated src=- shape=a1b5ec72 vocab=37b0c794
-/
theorem chain_sdiff_diagonal_subset_pair_sdiff_diagonal {x r h Y : ℕ} (hr : 2 ≤ r) :
    totientChainSet x r h \ aboveCutoffDiagonalSet x h Y ⊆
      shiftedEqualTotientSet x h \ aboveCutoffDiagonalSet x h Y := by
  exact Finset.sdiff_subset_sdiff_left (aboveCutoffDiagonalSet x h Y)
    (totientChainSet_subset_shiftedEqualTotientSet hr)

/-- The chain off-diagonal cardinality is exactly subtraction of its diagonal count.
@isnad1 id=eq.0h4v.s5.da9b3032ee11 from=translated src=- shape=0a006767 vocab=5e643315
-/
theorem totientChainCount_sub_firstPairDiagonalChainCount (x r h Y : ℕ) :
    totientChainCount x r h - firstPairDiagonalChainCount x r h Y =
      (totientChainSet x r h \ aboveCutoffDiagonalSet x h Y).card := by
  classical
  rw [totientChainCount, firstPairDiagonalChainCount, firstPairDiagonalChainSet]
  rw [← Finset.card_sdiff_of_subset Finset.inter_subset_left]
  congr 1
  ext n
  simp

/-- The pair off-diagonal cardinality is likewise an exact subtraction.
@isnad1 id=eq.0h3v.s5.8c4ae4fc3a53 from=translated src=- shape=31503510 vocab=283baf2d
-/
theorem shiftedEqualTotientCount_sub_aboveCutoffDiagonalCount (x h Y : ℕ) :
    shiftedEqualTotientCount x h - aboveCutoffDiagonalCount x h Y =
      (shiftedEqualTotientSet x h \ aboveCutoffDiagonalSet x h Y).card := by
  rw [shiftedEqualTotientCount, aboveCutoffDiagonalCount]
  exact (Finset.card_sdiff_of_subset
    (aboveCutoffDiagonalSet_subset_shiftedEqualTotientSet x h Y)).symm

/-- The exact finite cardinality inequality used in the proof of Corollary 11.1.
@isnad1 id=le.1h4v.s5.2b25f989d702 from=translated src=- shape=f6a8835a vocab=efa54203
-/
theorem chain_offDiagonal_cardinality_le_pair_offDiagonal_cardinality {x r h Y : ℕ}
    (hr : 2 ≤ r) :
    totientChainCount x r h - firstPairDiagonalChainCount x r h Y ≤
      shiftedEqualTotientCount x h - aboveCutoffDiagonalCount x h Y := by
  rw [totientChainCount_sub_firstPairDiagonalChainCount,
    shiftedEqualTotientCount_sub_aboveCutoffDiagonalCount]
  exact Finset.card_le_card (chain_sdiff_diagonal_subset_pair_sdiff_diagonal hr)

/-- Both inequalities displayed in the set-theoretic proof of Corollary 11.1.
@isnad1 id=and.1h4v.s6.4b275e0a200b from=translated src=- shape=780a35a9 vocab=efa54203
-/
theorem chain_offDiagonal_cardinality_bounds {x r h Y : ℕ} (hr : 2 ≤ r) :
    0 ≤ totientChainCount x r h - firstPairDiagonalChainCount x r h Y ∧
      totientChainCount x r h - firstPairDiagonalChainCount x r h Y ≤
        shiftedEqualTotientCount x h - aboveCutoffDiagonalCount x h Y :=
  ⟨Nat.zero_le _, chain_offDiagonal_cardinality_le_pair_offDiagonal_cardinality hr⟩

/-- Odd shifts have no first-pair diagonal chain integers.
@isnad1 id=eq.1h4v.s4.45d386c680dd from=translated src=- shape=76e91cb8 vocab=d07785e3
-/
theorem firstPairDiagonalChainSet_eq_empty_of_odd {x r h Y : ℕ} (hodd : Odd h) :
    firstPairDiagonalChainSet x r h Y = ∅ := by
  classical
  rw [firstPairDiagonalChainSet, aboveCutoffDiagonalSet_eq_empty_of_odd hodd]
  exact Finset.inter_empty _

/-- Thus the first-pair diagonal chain count vanishes for odd shifts.
@isnad1 id=eq.1h4v.s4.50771999c086 from=translated src=- shape=a5678421 vocab=950ff9d3
-/
theorem firstPairDiagonalChainCount_eq_zero_of_odd {x r h Y : ℕ} (hodd : Odd h) :
    firstPairDiagonalChainCount x r h Y = 0 := by
  rw [firstPairDiagonalChainCount, firstPairDiagonalChainSet_eq_empty_of_odd hodd]
  rfl

/-- A chain of length two is exactly one shifted equal-totient equation.
@isnad1 id=iff.0h2v.s4.0d2c866aa4a7 from=translated src=- shape=ece4564a vocab=d9a1e25e
-/
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

/-- The length-two chain set is the shifted equal-totient set.
@isnad1 id=eq.0h2v.s4.d434d70455f4 from=translated src=- shape=d891494c vocab=963efdb4
-/
@[simp]
theorem totientChainSet_two (x h : ℕ) :
    totientChainSet x 2 h = shiftedEqualTotientSet x h := by
  classical
  ext n
  simp

/-- The length-two chain count is the shifted equal-totient count.
@isnad1 id=eq.0h2v.s4.b9eff2027c61 from=translated src=- shape=4bafb05e vocab=62712874
-/
@[simp]
theorem totientChainCount_two (x h : ℕ) :
    totientChainCount x 2 h = shiftedEqualTotientCount x h := by
  rw [totientChainCount, shiftedEqualTotientCount, totientChainSet_two]

/-- At length two, the first-pair chain diagonal is the full pair diagonal.
@isnad1 id=eq.0h3v.s4.5ca74a0d8e56 from=translated src=- shape=eadd4d97 vocab=880efbd2
-/
@[simp]
theorem firstPairDiagonalChainSet_two (x h Y : ℕ) :
    firstPairDiagonalChainSet x 2 h Y = aboveCutoffDiagonalSet x h Y := by
  classical
  rw [firstPairDiagonalChainSet, totientChainSet_two]
  exact Finset.inter_eq_right.mpr
    (aboveCutoffDiagonalSet_subset_shiftedEqualTotientSet x h Y)

/-- The corresponding length-two diagonal counts agree.
@isnad1 id=eq.0h3v.s4.50c106a3c537 from=translated src=- shape=9ea3c937 vocab=5c9987c1
-/
@[simp]
theorem firstPairDiagonalChainCount_two (x h Y : ℕ) :
    firstPairDiagonalChainCount x 2 h Y = aboveCutoffDiagonalCount x h Y := by
  rw [firstPairDiagonalChainCount, aboveCutoffDiagonalCount,
    firstPairDiagonalChainSet_two]

/-- At length two, the chain and pair off-diagonal cardinalities are identical.
@isnad1 id=eq.0h3v.s5.11f879d2352c from=translated src=- shape=3e598ae3 vocab=96d7842d
-/
@[simp, nolint simpNF]
theorem chain_offDiagonal_cardinality_two (x h Y : ℕ) :
    totientChainCount x 2 h - firstPairDiagonalChainCount x 2 h Y =
      shiftedEqualTotientCount x h - aboveCutoffDiagonalCount x h Y := by
  rw [totientChainCount_two, firstPairDiagonalChainCount_two]

end RankAmplification
