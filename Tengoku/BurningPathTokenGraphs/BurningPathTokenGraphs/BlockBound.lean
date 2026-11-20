import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.BlockCover
import Tengoku.Seed.Order.Lattice.Nat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The exact finite block upper-bound expression

This file packages the minimum over `1 ≤ s ≤ n` appearing in part (B).
-/

namespace BurningPath

/-- The finite constructive bound associated with block length `s`.-/
def blockUpperBound (n k s : ℕ) : ℕ :=
  Nat.choose (n ⌈/⌉ s + k - 1) k + k * (s - 1)

/-- A natural number is one of the admissible finite block bounds.-/
def IsBlockUpperBoundValue (n k t : ℕ) : Prop :=
  ∃ s, 1 ≤ s ∧ s ≤ n ∧ t = blockUpperBound n k s

theorem exists_isBlockUpperBoundValue {n k : ℕ} (hn : 1 ≤ n) :
    ∃ t, IsBlockUpperBoundValue n k t := by
  exact ⟨blockUpperBound n k 1, 1, le_rfl, hn, rfl⟩

/-- The exact minimum over all admissible block lengths.-/
noncomputable def optimalBlockUpperBound (n k : ℕ) : ℕ :=
  sInf {t | IsBlockUpperBoundValue n k t}

theorem optimalBlockUpperBound_spec {n k : ℕ} (hn : 1 ≤ n) :
    IsBlockUpperBoundValue n k (optimalBlockUpperBound n k) :=
  Nat.sInf_mem (exists_isBlockUpperBoundValue hn)

theorem optimalBlockUpperBound_le {n k s : ℕ} (hs : 1 ≤ s) (hsn : s ≤ n) :
    optimalBlockUpperBound n k ≤ blockUpperBound n k s :=
  Nat.sInf_le ⟨s, hs, hsn, rfl⟩

/-- Every individual block expression supports an explicit-metric ranked cover.-/
theorem hasPathMetricRankedCover_blockUpperBound {n k s : ℕ}
    (hk : k ≤ n) (hs : 1 ≤ s) :
    HasPathMetricRankedCover n k (blockUpperBound n k s) := by
  simpa [blockUpperBound] using hasPathMetricRankedCover_blockBound hk s hs

end BurningPath
