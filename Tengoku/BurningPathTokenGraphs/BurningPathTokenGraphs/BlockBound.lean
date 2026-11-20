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

/--
@isnad1 id=ex.1h2v.s4.639cae2802ab from=translated src=- shape=6fbd0ec0 vocab=8bc7e555
-/
theorem exists_isBlockUpperBoundValue {n k : ℕ} (hn : 1 ≤ n) :
    ∃ t, IsBlockUpperBoundValue n k t := by
  exact ⟨blockUpperBound n k 1, 1, le_rfl, hn, rfl⟩

/-- The exact minimum over all admissible block lengths.-/
noncomputable def optimalBlockUpperBound (n k : ℕ) : ℕ :=
  sInf {t | IsBlockUpperBoundValue n k t}

/--
@isnad1 id=isblocku.1h2v.s4.28d6e7321f66 from=translated src=- shape=e6cbdb34 vocab=d9e456b1
-/
theorem optimalBlockUpperBound_spec {n k : ℕ} (hn : 1 ≤ n) :
    IsBlockUpperBoundValue n k (optimalBlockUpperBound n k) :=
  Nat.sInf_mem (exists_isBlockUpperBoundValue hn)

/--
@isnad1 id=le.2h3v.s5.c2b64bbeed40 from=translated src=- shape=108c82dc vocab=bd9604a3
-/
theorem optimalBlockUpperBound_le {n k s : ℕ} (hs : 1 ≤ s) (hsn : s ≤ n) :
    optimalBlockUpperBound n k ≤ blockUpperBound n k s :=
  Nat.sInf_le ⟨s, hs, hsn, rfl⟩

/-- Every individual block expression supports an explicit-metric ranked cover.
@isnad1 id=haspathm.2h3v.s4.d15a3ce51682 from=translated src=- shape=b305c365 vocab=7f325632
-/
theorem hasPathMetricRankedCover_blockUpperBound {n k s : ℕ}
    (hk : k ≤ n) (hs : 1 ≤ s) :
    HasPathMetricRankedCover n k (blockUpperBound n k s) := by
  simpa [blockUpperBound] using hasPathMetricRankedCover_blockBound hk s hs

end BurningPath
