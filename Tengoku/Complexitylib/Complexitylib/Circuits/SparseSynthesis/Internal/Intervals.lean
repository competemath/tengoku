/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Tengoku.Complexitylib.Complexitylib.Circuits.SparseSynthesis.Internal.Chunks

/-!
# Intervals with few specified positions

Consecutive chunks of an ordered support can be masked by intervals. Masking
prevents an arbitrary completion of one chunk from changing the values
specified in another chunk.
-/

@[expose] public section

namespace Complexity.CircuitSparseSynthesis.Internal

/-- Position of the support element at `rank`, or the right endpoint `L` past the support. -/
def supportCut {L : ℕ} (s : Finset (Fin L)) (rank : ℕ) : Fin (L + 1) :=
  if h : rank < s.card then (s.orderEmbOfFin rfl ⟨rank, h⟩).castSucc else Fin.last L

/--
@isnad1 id=iff.1h4v.s8.d4475923b87a from=translated src=- shape=d201db1e vocab=f39abc0d
-/
theorem supportCut_le_iff {L : ℕ} (s : Finset (Fin L)) (rank : ℕ)
    (i : Fin L) (hi : i ∈ s) :
    (supportCut s rank).val ≤ i.val ↔ rank ≤ ((s.orderIsoOfFin rfl).symm ⟨i, hi⟩).val := by
  unfold supportCut
  split
  next h =>
    change s.orderIsoOfFin rfl ⟨rank, h⟩ ≤ ⟨i, hi⟩ ↔ _
    exact (s.orderIsoOfFin rfl).le_symm_apply.symm
  next h =>
    have lt := ((s.orderIsoOfFin rfl).symm ⟨i, hi⟩).isLt
    simp only [Fin.val_last]
    omega

/--
@isnad1 id=iff.1h4v.s8.0b0fb68a88ea from=translated src=- shape=0d62a132 vocab=908f059d
-/
theorem lt_supportCut_iff {L : ℕ} (s : Finset (Fin L)) (rank : ℕ)
    (i : Fin L) (hi : i ∈ s) :
    i.val < (supportCut s rank).val ↔ ((s.orderIsoOfFin rfl).symm ⟨i, hi⟩).val < rank := by
  simpa only [not_le] using not_congr (supportCut_le_iff s rank i hi)

/-- Specified positions between consecutive cuts, at most `K` positions per chunk. -/
def intervalChunk {L : ℕ} (s : Finset (Fin L)) (K block : ℕ) : Finset (Fin L) :=
  s.filter fun i => (supportCut s (block * K)).val ≤ i.val ∧
    i.val < (supportCut s ((block + 1) * K)).val

/--
@isnad1 id=iff.1h5v.s9.f6f0a9354bb2 from=translated src=- shape=7f3b57e2 vocab=e25fe036
-/
theorem mem_intervalChunk_iff {L : ℕ} (s : Finset (Fin L)) (K block : ℕ)
    (i : Fin L) (hi : i ∈ s) :
    i ∈ intervalChunk s K block ↔ block * K ≤ ((s.orderIsoOfFin rfl).symm ⟨i, hi⟩).val ∧
      ((s.orderIsoOfFin rfl).symm ⟨i, hi⟩).val < (block + 1) * K := by
  simp [intervalChunk, hi, supportCut_le_iff s _ i hi, lt_supportCut_iff s _ i hi]

/--
@isnad1 id=le.0h4v.s4.2e888eee5233 from=translated src=- shape=e8add24c vocab=57545b52
-/
theorem intervalChunk_card {L : ℕ} (s : Finset (Fin L)) (K block : ℕ) :
    (intervalChunk s K block).card ≤ K := by
  let rank (i : intervalChunk s K block) : ℕ :=
    ((s.orderIsoOfFin rfl).symm ⟨i.val, (Finset.mem_filter.mp i.property).1⟩).val
  have bounds (i : intervalChunk s K block) : block * K ≤ rank i ∧
      rank i < block * K + K := by
    simpa [rank, Nat.add_mul] using (mem_intervalChunk_iff s K block i.val
      (Finset.mem_filter.mp i.property).1).mp i.property
  let encode (i : intervalChunk s K block) : Fin K :=
    ⟨rank i - block * K, by have := bounds i; omega⟩
  have injective : Function.Injective encode := by
    intro a b hab
    have eqn := congrArg Fin.val hab
    have ha := bounds a
    have hb := bounds b
    have same : rank a = rank b := by dsimp [encode] at eqn; omega
    have eqRank := Fin.ext same
    have eqVal := (s.orderIsoOfFin rfl).symm.injective eqRank
    exact Subtype.ext (show a.val = b.val from congrArg (fun z : s => z.val) eqVal)
  simpa using Fintype.card_le_of_injective encode injective

/--
@isnad1 id=ex.2h4v.s7.b87cb100761a from=translated src=- shape=9d0504b4 vocab=d36c0649
-/
theorem exists_intervalChunk {L : ℕ} (s : Finset (Fin L)) (K : ℕ) (positive : 0 < K)
    (i : Fin L) (hi : i ∈ s) :
    ∃ block : Fin (s.card / K + 1), i ∈ intervalChunk s K block.val := by
  let rank := (s.orderIsoOfFin rfl).symm ⟨i, hi⟩
  let block : Fin (s.card / K + 1) :=
    ⟨rank.val / K, Nat.lt_succ_of_le (Nat.div_le_div_right rank.isLt.le)⟩
  refine ⟨block, (mem_intervalChunk_iff s K block.val i hi).mpr ?_⟩
  change rank.val / K * K ≤ rank.val ∧ rank.val < (rank.val / K + 1) * K
  constructor
  · exact Nat.div_mul_le_self _ _
  · exact (Nat.div_lt_iff_lt_mul positive).mp (Nat.lt_succ_self _)

end Complexity.CircuitSparseSynthesis.Internal
