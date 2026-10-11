module

public import Tengoku.Erdos1196.PrimitiveSetsAboveX.Basic
public import Tengoku

/-!
# First-entry row data

This file packages the row-wise data for the first-entry contribution to the normalization
constant. It introduces the threshold selecting admissible first jumps from a parent state `m`,
the resulting tail sum, and the pairwise weights used later in the fiberwise reindexing of
`B_x`.

## Main definitions

* `entryThreshold`
* `firstEntryTail`
* `firstEntryPairWeight`
-/

@[expose] public section

open scoped ArithmeticFunction BigOperators

namespace PrimitiveSetsAboveX

/-- The least threshold satisfying both `q ≥ Y` and `x ≤ m * q`. -/
def entryThreshold (x Y m : ℕ) : ℕ :=
  max Y (x ⌈/⌉ m)

/-- The first-entry tail sum starting from a parent state `m`. -/
noncomputable def firstEntryTail (x Y m : ℕ) : ℝ :=
  ∑' q : ℕ,
    if entryThreshold x Y m ≤ q then
      Λ q / ((q : ℝ) * (Real.log ((m * q : ℕ) : ℝ)) ^ 2)
    else 0

/-- The pairwise weight indexed by a parent state `m` and jump factor `q`
for the first-entry contribution to `B_x`. -/
noncomputable def firstEntryPairWeight (x Y : ℕ) (mq : ℕ × ℕ) : ℝ :=
  if 1 ≤ mq.1 ∧ mq.1 < x ∧ entryThreshold x Y mq.1 ≤ mq.2 then
    Λ mq.2 / (((mq.1 * mq.2 : ℕ) : ℝ) * (Real.log ((mq.1 * mq.2 : ℕ) : ℝ)) ^ 2)
  else 0

/-- The lower-threshold condition is exactly the conjunction `q ≥ Y` and `x ≤ m * q`. -/
lemma entryThreshold_le_iff (x Y m q : ℕ) (hm : 0 < m) :
    entryThreshold x Y m ≤ q ↔ Y ≤ q ∧ x ≤ m * q := by
  rw [entryThreshold, max_le_iff]
  constructor
  · rintro ⟨hY, hq⟩
    exact ⟨hY, (ceilDiv_le_iff_le_mul hm).1 hq⟩
  · rintro ⟨hY, hxq⟩
    exact ⟨hY, (ceilDiv_le_iff_le_mul hm).2 hxq⟩

end PrimitiveSetsAboveX
