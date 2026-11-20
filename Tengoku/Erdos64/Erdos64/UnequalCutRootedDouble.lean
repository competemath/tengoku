import Tengoku.Erdos64.Erdos64.UnequalCutRootSide
import Tengoku.Erdos64.Erdos64.RootedDoubleDegreeOrder
import Tengoku.Erdos64.Erdos64.RootedDoubleCycleLocalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-
An unequal two-sided cut can be folded into a rooted double of the smaller
side.  The double repairs the possible degree-two root: every nonroot keeps
its ambient degree, while the shared root receives two copies of its internal
side degree.  The rooted-double localization theorem then transfers every
simple cycle back to the ambient graph with the same length.
-/
/--
@isnad1 id=false.7h5v.s7.b06f5437b052 from=translated src=- shape=edcd6b86 vocab=f937f190
-/
theorem MinimalCounterexample.false_of_unequal_cut_root_partition
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (minimalCounterexample : EdgeMinimalCounterexample G)
    (A B : Finset V) (r : V)
    (hpartition : A ∪ B = Finset.univ)
    (hinter : A ∩ B = ({r} : Finset V))
    (hnocross : ∀ x, x ∈ A → x ≠ r →
      ∀ y, y ∈ B → y ≠ r → ¬G.Adj x y)
    (hrootA : 2 ≤ internalDegree G A r)
    (hrootB : 2 ≤ internalDegree G B r)
    (hAB : A.card < B.card) :
    False := by
  classical
  obtain ⟨S, root, hclosed, hroot, hsize⟩ :=
    exists_unequal_cut_root_side
      minimalCounterexample.vertexMinimal.isSubgraphCritical
      A B r hpartition hinter hnocross hrootA hrootB hAB
  have hside : ∀ v, v ∈ S → 3 ≤ G.degree v := by
    intro v hv
    exact degree_ge_three_of_minDegree_ge_three G
      minimalCounterexample.vertexMinimal.isCounterexample.1 v
  have horder := rootedDouble_degree_order_interface
    (G := G) S root hclosed hroot hside hsize
  let W := RootedDoubleVertex (↑S : Set V) root
  let H : SimpleGraph W :=
    rootedDoubleGraph (G.induce (↑S : Set V)) root
  letI : Fintype W := inferInstance
  letI : DecidableRel H.Adj := inferInstance
  letI : Nonempty W := ⟨none⟩
  have hHmin : H.minDegree ≥ 3 := by
    apply SimpleGraph.le_minDegree_of_forall_le_degree (G := H) 3
    intro z
    cases z with
    | none =>
        have hrootdeg := horder.2.1
        simpa [H, W] using (show 3 ≤
          (rootedDoubleGraph (G.induce (↑S : Set V)) root).degree none by omega)
    | some z =>
        rcases z with ⟨b, v⟩
        simpa [H, W] using horder.1 b v
  have hHno : ¬ HasPowerOfTwoCycle H := by
    intro hcycle
    rcases hcycle with ⟨k, z, c, hk, hc, hlen⟩
    obtain ⟨hproj, hproj_len⟩ :=
      rootedDouble_cycle_localization_projection
        (G := G.induce (↑S : Set V)) (r := root) c hc
    let e : G.induce (↑S : Set V) ↪g G :=
      SimpleGraph.Embedding.induce (G := G) (↑S : Set V)
    have hambient : ((c.map rootedDoubleProjectionHom).map e.toHom).IsCycle :=
      hproj.map e.injective
    have hambient_len :
        ((c.map rootedDoubleProjectionHom).map e.toHom).length = 2 ^ k := by
      rw [SimpleGraph.Walk.length_map, SimpleGraph.Walk.length_map]
      exact hlen
    apply minimalCounterexample.vertexMinimal.isCounterexample.2
    exact ⟨k, e (rootedDoubleProjectionHom z),
      (c.map rootedDoubleProjectionHom).map e.toHom, hk, hambient,
      hambient_len⟩
  have hsmall : IsStrictlySmallerCounterexample G H :=
    ⟨⟨hHmin, hHno⟩, by simpa [H, W] using horder.2.2.2⟩
  exact minimalCounterexample.vertexMinimal.not_exists_strictly_smaller hsmall

end Erdos64
