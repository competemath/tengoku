import Tengoku.Seed.Algebra.Field.Defs
import Tengoku.Seed.Data.Set.Finite.Basic
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Algebra.OrderPattern

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Proof of Lemma B.10

Uses `OrderPattern.exists_infinite_order_homogeneous` (`Algebra/OrderPattern.lean`).
-/

namespace AlternatingAnalyticChallenge.LemB_10

universe u

/-- For every `T : ℕ^N → L` there is an infinite `H ⊆ ℕ` on which `T` depends only on the
pattern of its argument.-/
theorem exists_infinite_pattern_homogeneous
    {L : Type u} [Field L] [Finite L] (N : ℕ) (hN : 1 ≤ N) (T : (Fin N → ℕ) → L) :
    ∃ H : Set ℕ, H.Infinite ∧
      ∀ z z' : Fin N → ℕ, (∀ i, z i ∈ H) → (∀ i, z' i ∈ H) →
        (∀ i j, (z i < z j ↔ z' i < z' j) ∧ (z i = z j ↔ z' i = z' j)) →
        T z = T z' := by
  exact OrderPattern.exists_infinite_order_homogeneous N T

end AlternatingAnalyticChallenge.LemB_10
