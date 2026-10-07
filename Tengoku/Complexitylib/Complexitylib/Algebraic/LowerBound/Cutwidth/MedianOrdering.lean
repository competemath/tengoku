/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition
public import Tengoku

/-!
# Ordering a cubic graph by median edge positions

Given a path decomposition of a simple 3-regular graph, place every edge at a
position inside a bag containing its endpoints, so that positions are
distinct and increase with the bag index. Each vertex has three incident
positions; order the vertices by the middle one. Then every prefix cut has at
most one more edge than the bag in which the last vertex's median edge lies:
a crossing edge below the median of the last vertex is the unique low edge of
its later endpoint, one above it is the unique high edge of its earlier
endpoint, and the median itself is a single edge. Each charged vertex lies in
that bag by consecutiveness.

The main result is `card_cutFinset_key_lt_le`: with bags of size at most
`p + 1`, an injective key orders the vertices so that every prefix cut has at
most `p + 2` edges.
-/

@[expose] public section

namespace Algebraic
namespace Cutwidth

open scoped Classical

namespace MedianOrdering

variable {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
  (D : PathDecomposition H)

/-! ### Bags indexed by natural numbers -/

/-- The bag with index `i`, or the empty set beyond the decomposition. -/
noncomputable def bagN (i : Nat) : Finset W :=
  if h : i < D.length then D.bag ⟨i, h⟩ else ∅

omit [Fintype W] [DecidableEq W] [DecidableRel H.Adj] in
theorem card_bagN_le {p : Nat} (hbag : ∀ i, (D.bag i).card ≤ p + 1) (i : Nat) :
    (bagN H D i).card ≤ p + 1 := by
  unfold bagN
  split_ifs
  · exact hbag _
  · simp

omit [Fintype W] [DecidableEq W] [DecidableRel H.Adj] in
theorem bagN_consecutive {w : W} {i j k : Nat} (hij : i ≤ j) (hjk : j ≤ k)
    (hi : w ∈ bagN H D i) (hk : w ∈ bagN H D k) : w ∈ bagN H D j := by
  have hk' : k < D.length := by
    by_contra h
    simp [bagN, h] at hk
  have hi' : i < D.length := by omega
  have hj' : j < D.length := by omega
  simp only [bagN, hi', hj', hk', ↓reduceDIte] at hi hk ⊢
  exact D.consecutive w ⟨i, hi'⟩ ⟨j, hj'⟩ ⟨k, hk'⟩ hij hjk hi hk

/-- The first bag containing both endpoints of an edge; `0` if none exists. -/
noncomputable def bagOf (e : Sym2 W) : Nat :=
  if h : ∃ i : Nat, ∀ a ∈ e, a ∈ bagN H D i then Nat.find h else 0

omit [DecidableRel H.Adj] in
theorem mem_bagN_bagOf {e : Sym2 W} (he : e ∈ H.edgeSet) {a : W} (ha : a ∈ e) :
    a ∈ bagN H D (bagOf H D e) := by
  induction e using Sym2.ind with
  | _ u v =>
    obtain ⟨i, hu, hv⟩ := D.edge_mem u v he
    have h : ∃ j : Nat, ∀ a ∈ s(u, v), a ∈ bagN H D j := by
      refine ⟨i.val, ?_⟩
      intro a ha
      simp only [bagN, i.isLt, ↓reduceDIte, Fin.eta]
      rcases Sym2.mem_iff.mp ha with rfl | rfl <;> assumption
    simp only [bagOf, h, ↓reduceDIte]
    exact Nat.find_spec h a ha

omit [DecidableRel H.Adj] in
/-- An edge is placed no later than any bag containing both endpoints. -/
theorem bagOf_le {e : Sym2 W} (i : Fin D.length)
    (he : ∀ a ∈ e, a ∈ D.bag i) : bagOf H D e ≤ i.val := by
  have hi : ∀ a ∈ e, a ∈ bagN H D i.val := by
    simpa only [bagN, i.isLt, ↓reduceDIte, Fin.eta] using he
  have h : ∃ j : Nat, ∀ a ∈ e, a ∈ bagN H D j := ⟨i.val, hi⟩
  simp only [bagOf, h, ↓reduceDIte]
  exact Nat.find_min' h hi

/-! ### Edge positions -/

/-- An injective rank of the edges. -/
noncomputable def rank (e : Sym2 W) : Nat :=
  (Fintype.equivFin (Sym2 W) e).val

omit [DecidableEq W] in
theorem rank_lt (e : Sym2 W) : rank e < Fintype.card (Sym2 W) :=
  (Fintype.equivFin (Sym2 W) e).isLt

omit [DecidableEq W] in
theorem rank_injective : Function.Injective (rank : Sym2 W → Nat) :=
  fun _ _ h => (Fintype.equivFin (Sym2 W)).injective (Fin.ext h)

/-- The position of an edge: its bag index, refined by its rank. -/
noncomputable def pos (e : Sym2 W) : Nat :=
  bagOf H D e * Fintype.card (Sym2 W) + rank e

/-- Mixed-radix comparison: the leading digit is monotone. -/
theorem digit_le_of_le {b b' r r' c : Nat} (hr' : r' < c)
    (h : b * c + r ≤ b' * c + r') : b ≤ b' := by
  by_contra hlt
  rw [not_le] at hlt
  have : (b' + 1) * c ≤ b * c := Nat.mul_le_mul_right _ hlt
  rw [Nat.add_mul, one_mul] at this
  omega

omit [DecidableRel H.Adj] in
theorem pos_injective : Function.Injective (pos H D) := by
  intro e e' h
  have h₁ := digit_le_of_le (rank_lt e') h.le
  have h₂ := digit_le_of_le (rank_lt e) h.ge
  have hb : bagOf H D e = bagOf H D e' := le_antisymm h₁ h₂
  apply rank_injective
  unfold pos at h
  rw [hb] at h
  omega

omit [DecidableRel H.Adj] in
theorem bagOf_le_of_pos_le {e e' : Sym2 W} (h : pos H D e ≤ pos H D e') :
    bagOf H D e ≤ bagOf H D e' :=
  digit_le_of_le (rank_lt e') h

/-! ### Incident edges and medians -/

variable (regular : H.IsRegularOfDegree 3)

/-! ### The vertex ordering -/

end MedianOrdering

end Cutwidth
end Algebraic
