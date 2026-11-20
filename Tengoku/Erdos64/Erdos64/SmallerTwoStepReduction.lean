import Tengoku.Erdos64.Erdos64.TwoStepCycleLift
import Tengoku.Erdos64.Erdos64.TwoDegenerateEdgeBound
import Tengoku.Erdos64.Erdos64.RootDeletedNoDyadicTransfer

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- A middle vertex witnesses that a nontrivial two-step realization uses
strictly more vertices than its source.
@isnad1 id=lt.1h7v.s5.1c083a9bf14a from=translated src=- shape=4e8fcf12 vocab=25189246
-/
theorem TwoStepEmbedding.card_lt_of_adj
    {V W : Type u} {G : SimpleGraph V} {H : SimpleGraph W}
    [Fintype V] [Fintype W]
    (E : TwoStepEmbedding H G) {a b : W} (hab : H.Adj a b) :
    Fintype.card W < Fintype.card V := by
  apply Fintype.card_lt_of_injective_of_notMem E.vertex E.vertex.injective
    (b := E.middle ⟨s(a, b), hab⟩)
  rintro ⟨w, hw⟩
  exact E.disjoint w _ hw

/-- Every nonempty induced carrier of a smaller dyadic-free graph has a vertex
of degree at most two, by the defining vertex minimality of a counterexample.
@isnad1 id=ex.4h5v.s6.d32ee08d5d5c from=translated src=- shape=098c160e vocab=1316fc45
-/
theorem MinimalCounterexample.smaller_dyadic_free_has_low_internal_degree
    {V W : Type u} {G : SimpleGraph V} {H : SimpleGraph W}
    [Fintype V] [DecidableRel G.Adj]
    [Fintype W] [DecidableEq W] [DecidableRel H.Adj]
    (M : MinimalCounterexample G)
    (hsmall : Fintype.card W < Fintype.card V)
    (hno : ¬ HasPowerOfTwoCycle H)
    (S : Finset W) (hS : S.Nonempty) :
    ∃ w ∈ S, internalDegree H S w ≤ 2 := by
  classical
  by_contra hnot
  have hdegrees : ∀ w ∈ S, 3 ≤ internalDegree H S w := by
    intro w hw
    by_contra hlt
    exact hnot ⟨w, hw, by omega⟩
  let K : SimpleGraph (↑S : Set W) := H.induce (↑S : Set W)
  let : Nonempty (↑S : Set W) := hS.to_subtype
  have hmin : 3 ≤ K.minDegree := by
    apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro w
    change 3 ≤ (H.induce (↑S : Set W)).degree w
    rw [degree_induce_coeFinset_eq_internalDegree]
    exact hdegrees w.1 w.2
  have hcard : Fintype.card (↑S : Set W) < Fintype.card V :=
    lt_of_le_of_lt (Fintype.card_subtype_le _) hsmall
  exact M.not_exists_strictly_smaller
    ⟨⟨hmin, fun hc => hno (hasPowerOfTwoCycle_of_induce hc)⟩, hcard⟩

/-- A graph realized by distinct two-edge paths in a minimal counterexample
is two-degenerate whenever it has fewer vertices than that counterexample.
@isnad1 id=ex.3h6v.s6.4daa4b9329dd from=translated src=- shape=8243dee6 vocab=0d180296
-/
theorem MinimalCounterexample.smaller_twoStep_has_low_internal_degree
    {V W : Type u} {G : SimpleGraph V} {H : SimpleGraph W}
    [Fintype V] [DecidableRel G.Adj]
    [Fintype W] [DecidableEq W] [DecidableRel H.Adj]
    (M : MinimalCounterexample G) (E : TwoStepEmbedding H G)
    (hsmall : Fintype.card W < Fintype.card V)
    (S : Finset W) (hS : S.Nonempty) :
    ∃ w ∈ S, internalDegree H S w ≤ 2 :=
  M.smaller_dyadic_free_has_low_internal_degree hsmall
    (fun hc => M.isCounterexample.2 (E.hasPowerOfTwoCycle hc)) S hS

/-- Sharp edge bound for a smaller graph realized by two-edge paths in a
minimal counterexample.
@isnad1 id=le.3h5v.s6.478bc33208ef from=translated src=- shape=5ed81e5a vocab=0be4cafc
-/
theorem MinimalCounterexample.smaller_twoStep_edge_bound
    {V W : Type u} {G : SimpleGraph V} {H : SimpleGraph W}
    [Fintype V] [DecidableRel G.Adj]
    [Fintype W] [DecidableEq W] [DecidableRel H.Adj]
    (M : MinimalCounterexample G) (E : TwoStepEmbedding H G)
    (hsmall : Fintype.card W < Fintype.card V)
    (hn : 2 ≤ Fintype.card W) :
    H.edgeFinset.card + 3 ≤ 2 * Fintype.card W :=
  two_degenerate_edge_bound H
    (M.smaller_twoStep_has_low_internal_degree E hsmall) hn

/-- The smaller-order premise is automatic when a two-step realization has
an edge; if it has no edges, every internal degree is zero.
@isnad1 id=ex.2h6v.s6.bb846fb68ed2 from=translated src=- shape=67046560 vocab=542d2fd5
-/
theorem MinimalCounterexample.twoStep_has_low_internal_degree
    {V W : Type u} {G : SimpleGraph V} {H : SimpleGraph W}
    [Fintype V] [DecidableRel G.Adj]
    [Fintype W] [DecidableEq W] [DecidableRel H.Adj]
    (M : MinimalCounterexample G) (E : TwoStepEmbedding H G)
    (S : Finset W) (hS : S.Nonempty) :
    ∃ w ∈ S, internalDegree H S w ≤ 2 := by
  classical
  by_cases hedge : ∃ a b, H.Adj a b
  · obtain ⟨a, b, hab⟩ := hedge
    exact M.smaller_twoStep_has_low_internal_degree E (E.card_lt_of_adj hab) S hS
  · obtain ⟨w, hw⟩ := hS
    refine ⟨w, hw, ?_⟩
    have hzero : S.filter (H.Adj w) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hedge ⟨w, z, (Finset.mem_filter.mp hz).2⟩
    simp only [internalDegree, hzero, Finset.card_empty, Nat.zero_le]

/-- A vertex-minimal counterexample contains no two-step realization of a
finite graph of minimum degree at least three.
@isnad1 id=false.2h5v.s5.81fef15e6db1 from=translated src=- shape=9fc89f86 vocab=b428e6fe
-/
theorem MinimalCounterexample.not_twoStepEmbedding_of_minDegree_ge_three
    {V W : Type u} {G : SimpleGraph V} {H : SimpleGraph W}
    [Fintype V] [DecidableRel G.Adj]
    [Fintype W] [DecidableEq W] [DecidableRel H.Adj]
    (M : MinimalCounterexample G) (hmin : 3 ≤ H.minDegree)
    (E : TwoStepEmbedding H G) : False := by
  classical
  have hnonempty : Nonempty W := by
    by_contra h
    let : IsEmpty W := ⟨fun w => h ⟨w⟩⟩
    simp at hmin
  have hS : (Finset.univ : Finset W).Nonempty := Finset.univ_nonempty
  obtain ⟨w, _, hw⟩ := M.twoStep_has_low_internal_degree E Finset.univ hS
  have hwdegree : H.degree w ≤ 2 := by
    simpa [internalDegree, ← SimpleGraph.neighborFinset_eq_filter] using hw
  have := H.minDegree_le_degree w
  omega

end Erdos64
