import Tengoku.Linearhadwiger.HadwigerLean.Graph.RootedCliqueMinor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Pulling separations through an edge contraction

The preimages of the two shores under a connected partition form a
separation in the original graph. For a single edge contraction its
boundary is at most one vertex larger than the quotient boundary.
-/

namespace HadwigerLean

universe u v

namespace VertexSeparation

/-- Preimages of a quotient separation form a separation.-/
noncomputable def pullbackPartition {V : Type u} {I : Type v}
    {G : SimpleGraph V} (P : ConnectedPartition G I)
    (S : VertexSeparation P.touchingQuotient) : VertexSeparation G where
  left := {x | P.index x ∈ S.left}
  right := {x | P.index x ∈ S.right}
  cover := by
    ext x
    change P.index x ∈ S.left ∪ S.right ↔ x ∈ Set.univ
    rw [S.cover]
    simp
  no_cross := by
    intro x y hxL hxNR hyR hyNL hxy
    change P.index x ∈ S.left at hxL
    change P.index x ∉ S.right at hxNR
    change P.index y ∈ S.right at hyR
    change P.index y ∉ S.left at hyNL
    have hne : P.index x ≠ P.index y := by
      intro heq
      exact hxNR (by simpa [heq] using hyR)
    have hq : P.touchingQuotient.Adj (P.index x) (P.index y) :=
      ⟨hne, x, P.index_mem x, y, P.index_mem y, hxy⟩
    exact S.no_cross hxL hxNR hyR hyNL hq

/-- A branch whose quotient image is strictly far remains strictly far
when the separation is pulled back.-/
theorem branch_subset_strictRight_pullback
    {V : Type u} {I : Type v} {G : SimpleGraph V}
    (P : ConnectedPartition G I)
    (S : VertexSeparation P.touchingQuotient)
    (B : Set V)
    (hB : P.index '' B ⊆ S.strictRight) :
    B ⊆ (S.pullbackPartition P).strictRight := by
  intro x hx
  exact hB ⟨x, hx, rfl⟩

end VertexSeparation

/-- The index map of an edge contraction is injective after deleting one
endpoint of the contracted edge.-/
theorem edgeContractionIndex_injOn_away
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) :
    Set.InjOn (edgeContractionPartition G hab).index {x : V | x ≠ a} := by
  let P := edgeContractionPartition G hab
  intro x hx y hy hxy
  have hxm : x ∈ P.block (P.index x) := P.index_mem x
  have hym : y ∈ P.block (P.index x) := by
    rw [hxy]
    exact P.index_mem y
  change x ∈ edgeContractionBlock (a := a) (b := b) (P.index x) at hxm
  change y ∈ edgeContractionBlock (a := a) (b := b) (P.index x) at hym
  cases hq : P.index x with
  | none =>
    rw [hq] at hxm hym
    have hxab : x = a ∨ x = b := by
      simpa only [edgeContractionBlock, Set.mem_insert_iff, Set.mem_singleton_iff] using hxm
    have hyab : y = a ∨ y = b := by
      simpa only [edgeContractionBlock, Set.mem_insert_iff, Set.mem_singleton_iff] using hym
    rcases hxab with hxa | hxb
    · exact (hx hxa).elim
    rcases hyab with hya | hyb
    · exact (hy hya).elim
    exact hxb.trans hyb.symm
  | some z =>
    rw [hq] at hxm hym
    have hxz : x = z.1 := by
      simpa only [edgeContractionBlock, Set.mem_insert_iff, Set.mem_singleton_iff] using hxm
    have hyz : y = z.1 := by
      simpa only [edgeContractionBlock, Set.mem_insert_iff, Set.mem_singleton_iff] using hym
    exact hxz.trans hyz.symm
end HadwigerLean
