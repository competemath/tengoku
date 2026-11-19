import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
import Tengoku.Seed.Algebra.BigOperators.Ring.Finset
import Tengoku.Seed.Data.Real.Basic
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Averaging weighted yolks over quotient colors

This is the finite arithmetic step in Reed and Seymour's proof: if every piece
has a stable subset carrying at least half its weight, one color class of a
quotient coloring carries at least `1 / (2p)` of the total weight.
-/

namespace HadwigerLean

open Finset

/-- Among finitely many colors, one color class contains enough of the
half-weight choices. The graph-theoretic assertion that this union is stable
is handled separately.
@isnad1 id=ex.1h5v.s7.6175e3bf92b3 from=translated src=- shape=9946edee vocab=a8b7e780
-/
theorem exists_color_class_half_weight
    {I C : Type*} [Fintype I] [Fintype C] [Nonempty C] [DecidableEq C]
    (color : I → C) (pieceWeight yolkWeight : I → ℝ)
    (hhalf : ∀ i, pieceWeight i ≤ 2 * yolkWeight i) :
    ∃ c : C, (∑ i, pieceWeight i) ≤
      2 * (Fintype.card C : ℝ) *
        ∑ i, if color i = c then yolkWeight i else 0 := by
  classical
  have htotal : (∑ i, pieceWeight i) ≤ 2 * ∑ i, yolkWeight i := by
    calc
      (∑ i, pieceWeight i) ≤ ∑ i, 2 * yolkWeight i :=
        Finset.sum_le_sum (fun i _ => hhalf i)
      _ = 2 * ∑ i, yolkWeight i := by rw [mul_sum]
  have hpartition :
      (∑ c : C, ∑ i, if color i = c then yolkWeight i else 0) =
        ∑ i, yolkWeight i := by
    rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq]
  have hcard : (0 : ℝ) ≤ Fintype.card C := by exact_mod_cast Nat.zero_le _
  have hsum :
      (∑ c : C, (∑ i, pieceWeight i)) ≤
        ∑ c : C, 2 * (Fintype.card C : ℝ) *
          ∑ i, if color i = c then yolkWeight i else 0 := by
    calc
      (∑ c : C, (∑ i, pieceWeight i)) =
          (Fintype.card C : ℝ) * (∑ i, pieceWeight i) := by simp
      _ ≤ (Fintype.card C : ℝ) * (2 * ∑ i, yolkWeight i) :=
        mul_le_mul_of_nonneg_left htotal hcard
      _ = 2 * (Fintype.card C : ℝ) * (∑ c : C,
            ∑ i, if color i = c then yolkWeight i else 0) := by
        rw [hpartition]
        ring
      _ = ∑ c : C, 2 * (Fintype.card C : ℝ) *
            ∑ i, if color i = c then yolkWeight i else 0 := by rw [mul_sum]
  obtain ⟨c, _, hc⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨c, hc⟩

end HadwigerLean
