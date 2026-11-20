import Tengoku.QuartetDistanceBandeltDress.QuartetDistance.GraphQuartet
import Tengoku.QuartetDistanceBandeltDress.QuartetDistance.RibbonRestriction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Actual graph edges are circular intervals in every boundary word

This file joins the graph-theoretic edge positions of `GraphQuartet` to the
ribbon interval lemmas of `RibbonRestriction`.  The final statement is about
an arbitrary actual edge of `TreeAdequacy.PhyloTree.graph`: each of its two
delete-edge components contributes a circular interval of labels in every
boundary word.
-/

namespace QuartetDistance
namespace GraphRibbon

open SimpleGraph Tree
open GraphQuartet

/-! ## Edge positions as subtrees of the restored full tree -/

/--
@isnad1 id=issubtre.0h5v.s4.0f5dea77d19d from=translated src=- shape=5ba627bd vocab=2fbe62ee
-/
theorem isSubtree_map_of_properSubtree {α β : Type}
    {t : Tree.FullTree α} (p : GraphQuartet.FullTree.ProperSubtree t)
    (f : α → β) :
    RibbonRestriction.IsSubtree (p.tree.map f) (t.map f) := by
  induction p with
  | left l r =>
      exact .left (r.map f) (.here (l.map f))
  | right l r =>
      exact .right (l.map f) (.here (r.map f))
  | @inLeft l r p ih =>
      exact .left (r.map f) ih
  | @inRight l r p ih =>
      exact .right (l.map f) ih

namespace EdgePosition

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The ordinary full tree on the labels below an oriented graph edge.-/
def asFullSubtree {T : Tree.PhyloTree α}
    (p : GraphQuartet.PhyloTree.EdgePosition T) : Tree.FullTree α :=
  p.tree.map Subtype.val

/-- Every oriented graph edge supplies an actual subtree occurrence in the
restored full tree.
@isnad1 id=issubtre.0h3v.s5.0c96cc40b7bf from=translated src=- shape=c8ae5361 vocab=0d44a30e
-/
theorem asFullSubtree_isSubtree {T : Tree.PhyloTree α}
    (p : GraphQuartet.PhyloTree.EdgePosition T) :
    RibbonRestriction.IsSubtree (asFullSubtree p) T.asFullTree := by
  cases p with
  | crown =>
      exact .right (.leaf T.root) (.here (T.crown.map Subtype.val))
  | inside q =>
      exact .right (.leaf T.root)
        (isSubtree_map_of_properSubtree q Subtype.val)

/-- The leaf set of the restored subtree is exactly the graph edge cluster.
@isnad1 id=eq.0h3v.s5.e5a1f04a63a7 from=translated src=- shape=8ce533ce vocab=50abe92c
-/
@[simp] theorem asFullSubtree_leaves_toFinset {T : Tree.PhyloTree α}
    (p : GraphQuartet.PhyloTree.EdgePosition T) :
    (asFullSubtree p).leaves.toFinset = p.cluster := by
  ext a
  simp [asFullSubtree, GraphQuartet.PhyloTree.EdgePosition.cluster]

/-- The descendant side of every oriented edge is a circular interval in
every boundary word.
@isnad1 id=circular.1h4v.s5.1d01f6a2d495 from=translated src=- shape=b527a780 vocab=81925a73
-/
theorem cluster_circularInterval {T : Tree.PhyloTree α}
    (p : GraphQuartet.PhyloTree.EdgePosition T) {word : List α}
    (hword : word ∈ T.boundaryProfile) :
    RibbonRestriction.CircularInterval p.cluster word := by
  have hlinear := RibbonRestriction.boundary_linearInterval_edgeSide
    T (asFullSubtree_isSubtree p) hword
  rw [asFullSubtree_leaves_toFinset p] at hlinear
  exact hlinear.circular

/-- The complementary side of every oriented edge is also a circular
interval, possibly crossing the cut in the displayed boundary word.
@isnad1 id=circular.1h4v.s5.8723a047f3e8 from=translated src=- shape=618b47c6 vocab=33477f39
-/
theorem complement_circularInterval {T : Tree.PhyloTree α}
    (p : GraphQuartet.PhyloTree.EdgePosition T) {word : List α}
    (hword : word ∈ T.boundaryProfile) :
    RibbonRestriction.CircularInterval (Finset.univ \ p.cluster) word := by
  have h := RibbonRestriction.boundary_circularInterval_oppositeEdgeSide
    T (asFullSubtree_isSubtree p) hword
  rwa [asFullSubtree_leaves_toFinset p] at h

end EdgePosition

/-! ## Literal delete-edge components -/

namespace PhyloTree

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Labels in the component of `x` after deleting the actual edge `xy`.-/
noncomputable def edgeSide (T : Tree.PhyloTree α)
    (x y : TreeAdequacy.PhyloTree.Vertex T) : Finset α :=
  by
    classical
    exact Finset.univ.filter fun a =>
      ∃ z : TreeAdequacy.PhyloTree.Vertex T,
        TreeAdequacy.PhyloTree.label? T z = some a ∧
          ((TreeAdequacy.PhyloTree.graph T).deleteEdges {s(x, y)}).Reachable x z

/--
@isnad1 id=iff.0h5v.s6.631ccf110a58 from=translated src=- shape=ca60ba91 vocab=bcb176e4
-/
theorem mem_edgeSide_iff (T : Tree.PhyloTree α)
    (x y : TreeAdequacy.PhyloTree.Vertex T) (a : α) :
    a ∈ edgeSide T x y ↔
      ∃ z : TreeAdequacy.PhyloTree.Vertex T,
        TreeAdequacy.PhyloTree.label? T z = some a ∧
          ((TreeAdequacy.PhyloTree.graph T).deleteEdges
            {s(x, y)}).Reachable x z := by
  classical
  simp [edgeSide]

/-- The child component of a positioned edge has exactly its finite leaf
cluster as labels.
@isnad1 id=eq.0h3v.s5.55101fdb8761 from=translated src=- shape=6b18a7a2 vocab=3d43ddc9
-/
theorem edgeSide_child_parent_eq_cluster {T : Tree.PhyloTree α}
    (p : GraphQuartet.PhyloTree.EdgePosition T) :
    edgeSide T p.child p.parent = p.cluster := by
  ext a
  rw [mem_edgeSide_iff]
  have hedge : ({s(p.child, p.parent)} :
      Set (Sym2 (TreeAdequacy.PhyloTree.Vertex T))) =
      {s(p.parent, p.child)} := by
    rw [Sym2.eq_swap]
  rw [hedge]
  exact p.exists_label_reachable_iff a

/-- The parent component carries precisely the complementary cluster.
@isnad1 id=eq.0h3v.s5.bd34945d433b from=translated src=- shape=26fa55fe vocab=752d7fc8
-/
theorem edgeSide_parent_child_eq_complement {T : Tree.PhyloTree α}
    (p : GraphQuartet.PhyloTree.EdgePosition T) :
    edgeSide T p.parent p.child = Finset.univ \ p.cluster := by
  ext a
  rw [mem_edgeSide_iff]
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  exact p.exists_label_parent_reachable_iff a

/-- For every actual graph edge, the two label sets defined by delete-edge
reachability are complementary.
@isnad1 id=eq.1h4v.s6.59f219bacc7f from=translated src=- shape=cd375b58 vocab=16f98a56
-/
theorem edgeSide_reverse_eq_complement (T : Tree.PhyloTree α)
    {x y : TreeAdequacy.PhyloTree.Vertex T}
    (hxy : (TreeAdequacy.PhyloTree.graph T).Adj x y) :
    edgeSide T y x = Finset.univ \ edgeSide T x y := by
  obtain ⟨p, hp | hp⟩ :=
    GraphQuartet.PhyloTree.exists_edgePosition_of_adj T hxy
  · rw [hp.1, hp.2, edgeSide_child_parent_eq_cluster,
      edgeSide_parent_child_eq_complement]
    ext a
    simp
  · rw [hp.1, hp.2, edgeSide_parent_child_eq_complement,
      edgeSide_child_parent_eq_cluster]

/-- **Literal edge-interval lemma.**  For every actual edge `xy` of the
phylogenetic realization and every boundary word, the labels in the
delete-edge component of `x` and the labels in the delete-edge component of
`y` are both circular intervals.
@isnad1 id=and.2h5v.s6.44a0f62bc0a2 from=translated src=- shape=b1092a21 vocab=632828e8
-/
theorem edgeSides_circularIntervals (T : Tree.PhyloTree α)
    {x y : TreeAdequacy.PhyloTree.Vertex T}
    (hxy : (TreeAdequacy.PhyloTree.graph T).Adj x y)
    {word : List α} (hword : word ∈ T.boundaryProfile) :
    RibbonRestriction.CircularInterval (edgeSide T x y) word ∧
      RibbonRestriction.CircularInterval (edgeSide T y x) word := by
  obtain ⟨p, hp | hp⟩ :=
    GraphQuartet.PhyloTree.exists_edgePosition_of_adj T hxy
  · rw [hp.1, hp.2, edgeSide_parent_child_eq_complement,
      edgeSide_child_parent_eq_cluster]
    exact ⟨EdgePosition.complement_circularInterval p hword,
      EdgePosition.cluster_circularInterval p hword⟩
  · rw [hp.1, hp.2, edgeSide_child_parent_eq_cluster,
      edgeSide_parent_child_eq_complement]
    exact ⟨EdgePosition.cluster_circularInterval p hword,
      EdgePosition.complement_circularInterval p hword⟩

end PhyloTree

end GraphRibbon
end QuartetDistance
