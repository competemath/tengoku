import Tengoku.Seed.Algebra.Polynomial.Roots
import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Basic
import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F] [DecidableEq F]

/-!
# Multiplicity counting for LN97 Theorem 6.53

The first line of the proof of Theorem 6.53 uses the elementary fact

    M |T| <= deg h

when every element of the finite set `T` is a root of `h` of
multiplicity at least `M`.

This version deliberately avoids `∑ ... in ...` parser notation and
writes all finite sums as `Finset.sum ...` explicitly.
-/

/-- If every point of `T` is a root of `h` with multiplicity at least
`M > 0`, then `M * |T| ≤ natDegree h`.-/
theorem card_mul_le_natDegree_of_rootMultiplicity
    (h : Polynomial F) (T : Finset F) (M : ℕ)
    (hM : 0 < M)
    (hmult : ∀ c ∈ T, M ≤ rootMultiplicity c h) :
    M * T.card ≤ h.natDegree := by
  have hsub : T ⊆ h.roots.toFinset := by
    intro c hc
    have hpos : 0 < rootMultiplicity c h :=
      lt_of_lt_of_le hM (hmult c hc)
    have hcount : 0 < Multiset.count c h.roots := by
      simpa only [Polynomial.count_roots] using hpos
    have hmem : c ∈ h.roots := Multiset.count_pos.mp hcount
    simpa using hmem

  calc
    M * T.card =
        Finset.sum T (fun _ => M) := by
      simp [Nat.mul_comm]
    _ ≤ Finset.sum T (fun c => rootMultiplicity c h) := by
      apply Finset.sum_le_sum
      intro c hc
      exact hmult c hc
    _ = Finset.sum T (fun c => Multiset.count c h.roots) := by
      apply Finset.sum_congr rfl
      intro c hc
      exact (Polynomial.count_roots h).symm
    _ ≤ Finset.sum h.roots.toFinset
          (fun c => Multiset.count c h.roots) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro c hc hnot
      exact Nat.zero_le _
    _ = h.roots.card := by
      exact Multiset.toFinset_sum_count_eq h.roots
    _ ≤ h.natDegree := Polynomial.card_roots' h

end LN97
end MagicSquares
