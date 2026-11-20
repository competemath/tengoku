import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.PathMetric
import Tengoku.Seed.Algebra.Order.Floor.Div
import Tengoku.Seed.Data.Fin.Tuple.Sort
import Tengoku.Seed.Data.Sym.Card

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Block classification of path-token configurations

This file provides the finite block signatures used in the constructive burning upper bound.
-/

open scoped BigOperators

namespace BurningPath

/-- The number of consecutive blocks of length at most `s` needed to partition `Fin n`.-/
def blockCount (n s : ℕ) : ℕ :=
  n ⌈/⌉ s

/-- The index of the block containing a path vertex.-/
def blockIndex (n s : ℕ) (hs : 1 ≤ s) (x : Fin n) : Fin (blockCount n s) := by
  refine ⟨x.val / s, ?_⟩
  apply (Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt hs)).2
  exact x.isLt.trans_le <| by
    simpa [blockCount, nsmul_eq_mul, mul_comm] using
      (le_smul_ceilDiv (a := s) (b := n) (Nat.zero_lt_of_lt hs))

@[simp]
theorem blockIndex_val (n s : ℕ) (hs : 1 ≤ s) (x : Fin n) :
    (blockIndex n s hs x).val = x.val / s := by
  rfl

theorem blockIndex_monotone (n s : ℕ) (hs : 1 ≤ s) :
    Monotone (blockIndex n s hs) := by
  intro x y hxy
  apply Fin.mk_le_mk.mpr
  exact Nat.div_le_div_right hxy

/-- The weakly increasing sequence of blocks occupied by the ordered tokens.-/
noncomputable def blockCoordinates {n k : ℕ} (s : ℕ) (hs : 1 ≤ s)
    (A : Configuration (Fin n) k) : Fin k → Fin (blockCount n s) :=
  fun i ↦ blockIndex n s hs (coordinate A i)

theorem blockCoordinates_monotone {n k : ℕ} (s : ℕ) (hs : 1 ≤ s)
    (A : Configuration (Fin n) k) :
    Monotone (blockCoordinates s hs A) :=
  (blockIndex_monotone n s hs).comp (coordinate_strictMono A).monotone

/-- The multiset of blocks occupied by a `k`-token configuration.-/
abbrev BlockSignature (n k s : ℕ) :=
  Sym (Fin (blockCount n s)) k

/-- The block signature of a configuration, with repetitions recording multiple tokens per block.-/
noncomputable def blockSignature {n k : ℕ} (s : ℕ) (hs : 1 ≤ s)
    (A : Configuration (Fin n) k) : BlockSignature n k s :=
  Sym.mk (List.ofFn (blockCoordinates s hs A)) (by simp)

/-- There are exactly `choose (m + k - 1) k` possible signatures for `m` blocks.-/
theorem card_blockSignature (n k s : ℕ) :
    Fintype.card (BlockSignature n k s) =
      Nat.choose (blockCount n s + k - 1) k := by
  simpa [BlockSignature] using
    (Sym.card_sym_eq_choose (α := Fin (blockCount n s)) k)

/-- Equal signatures have equal weakly increasing block coordinates.-/
theorem blockCoordinates_eq_of_blockSignature_eq {n k : ℕ} (s : ℕ) (hs : 1 ≤ s)
    {A B : Configuration (Fin n) k} (h : blockSignature s hs A = blockSignature s hs B) :
    blockCoordinates s hs A = blockCoordinates s hs B := by
  have hmultiset :=
    congrArg
      (fun q : BlockSignature n k s => (q : Multiset (Fin (blockCount n s)))) h
  change
    (↑(List.ofFn (blockCoordinates s hs A)) : Multiset (Fin (blockCount n s))) =
      ↑(List.ofFn (blockCoordinates s hs B)) at hmultiset
  have hperm :
      (List.ofFn (blockCoordinates s hs A)).Perm
        (List.ofFn (blockCoordinates s hs B)) :=
    Multiset.coe_eq_coe.mp hmultiset
  exact List.ofFn_injective <|
    hperm.eq_of_pairwise'
      (blockCoordinates_monotone s hs A).sortedLE_ofFn.pairwise
      (blockCoordinates_monotone s hs B).sortedLE_ofFn.pairwise

private theorem natDist_le_pred_of_div_eq {a b s : ℕ} (hs : 1 ≤ s)
    (hdiv : a / s = b / s) :
    Nat.dist a b ≤ s - 1 := by
  have hspos : 0 < s := Nat.zero_lt_of_lt hs
  have ha_mod := Nat.mod_lt a hspos
  have hb_mod := Nat.mod_lt b hspos
  have ha_decomp := Nat.div_add_mod a s
  have hb_decomp := Nat.div_add_mod b s
  rw [hdiv] at ha_decomp
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab]
    omega
  · rw [Nat.dist_eq_sub_of_le_right hba]
    omega

/-- Corresponding ordered coordinates in the same blocks are at total distance at most `k(s-1)`.-/
theorem pathConfigurationDist_le_of_blockCoordinates_eq {n k : ℕ} (s : ℕ) (hs : 1 ≤ s)
    (A B : Configuration (Fin n) k)
    (h : blockCoordinates s hs A = blockCoordinates s hs B) :
    pathConfigurationDist A B ≤ k * (s - 1) := by
  simp only [pathConfigurationDist]
  calc
    (∑ i : Fin k, Nat.dist (coordinate A i).val (coordinate B i).val) ≤
        ∑ _i : Fin k, (s - 1) := by
      apply Finset.sum_le_sum
      intro i hi
      apply natDist_le_pred_of_div_eq hs
      have hi := congrFun h i
      exact congrArg Fin.val hi
    _ = k * (s - 1) := by simp

/-- Configurations with the same block signature are within the common block radius.-/
theorem pathConfigurationDist_le_of_blockSignature_eq {n k : ℕ} (s : ℕ) (hs : 1 ≤ s)
    (A B : Configuration (Fin n) k)
    (h : blockSignature s hs A = blockSignature s hs B) :
    pathConfigurationDist A B ≤ k * (s - 1) :=
  pathConfigurationDist_le_of_blockCoordinates_eq s hs A B
    (blockCoordinates_eq_of_blockSignature_eq s hs h)

end BurningPath
