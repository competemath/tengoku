import Tengoku.Erdos64.Erdos64.MinimalCounterexampleBalancedSides
import Tengoku.Erdos64.Erdos64.CutVertexComponentBoundary

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- If `x` lies in one root-deleted component, the other root-deleted
    component lies entirely in the component containing `r` after deleting
    `x`.  The proof lifts a path through the other component and its root
    attachment into the induced graph with `x` removed.-/
theorem MinimalCounterexample.rootDeleted_component_nested_in_other_root_component
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (r x : V)
    (C D : (G.induce {v : V | v ≠ r}).ConnectedComponent)
    (hCD : C ≠ D)
    (hxC : x ∈ rootDeletedComponentCarrier G r C)
    (A : (G.induce {v : V | v ≠ x}).ConnectedComponent)
    (hrA : r ∈ rootDeletedComponentCarrier G x A) :
    ∀ d, d ∈ rootDeletedComponentCarrier G r D →
      d ∈ rootDeletedComponentCarrier G x A := by
  classical
  have hxr : x ≠ r := by
    intro h
    subst x
    exact (rootDeletedComponentCarrier_nonempty_not_mem G r C).2 hxC
  have hxD : x ∉ rootDeletedComponentCarrier G r D := by
    intro hxD
    obtain ⟨hxne, hxCs⟩ :=
      (mem_rootDeletedComponentCarrier_iff G r C x).mp hxC
    obtain ⟨_, hxDs⟩ :=
      (mem_rootDeletedComponentCarrier_iff G r D x).mp hxD
    have hC :
        (G.induce {v : V | v ≠ r}).connectedComponentMk ⟨x, hxne⟩ = C :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff C ⟨x, hxne⟩).mp hxCs
    have hD :
        (G.induce {v : V | v ≠ r}).connectedComponentMk ⟨x, hxne⟩ = D :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff D ⟨x, hxne⟩).mp hxDs
    exact hCD (hC.symm.trans hD)
  intro d hdD
  obtain ⟨hdne, hdDs⟩ :=
    (mem_rootDeletedComponentCarrier_iff G r D d).mp hdD
  obtain ⟨a, haD, har⟩ :=
    (rootDeletedComponent_boundary r M.isConnected D).2
  obtain ⟨hane, haDs⟩ :=
    (mem_rootDeletedComponentCarrier_iff G r D a).mp haD
  obtain ⟨q, hq⟩ := D.connected_toSimpleGraph.exists_isPath
    (⟨⟨a, hane⟩, haDs⟩ : D) (⟨⟨d, hdne⟩, hdDs⟩ : D)
  let H : SimpleGraph {v : V // v ≠ x} := G.induce {v : V | v ≠ x}
  have hDsub :
      ∀ (v : {v : V // v ≠ r}), v ∈ D.supp →
        v.1 ∈ rootDeletedComponentCarrier G r D := by
    intro v hv
    exact (mem_rootDeletedComponentCarrier_iff G r D v.1).2 ⟨v.2, hv⟩
  have hDavoid :
      ∀ (v : {v : V // v ≠ r}), v ∈ D.supp → v.1 ≠ x := by
    intro v hv h
    exact hxD (h ▸ hDsub v hv)
  have hax : a ≠ x := hDavoid ⟨a, hane⟩ haDs
  have hdx : d ≠ x := hDavoid ⟨d, hdne⟩ hdDs
  have hrootx : r ≠ x := hxr.symm
  let e : D.toSimpleGraph →g H :=
    { toFun := fun v => ⟨v.1.1, hDavoid v.1 v.2⟩
      map_rel' := by
        intro u v huv
        exact huv }
  let q0 : H.Walk ⟨a, hax⟩ ⟨d, hdx⟩ := q.map e
  let q1 : H.Walk ⟨r, hrootx⟩ ⟨d, hdx⟩ :=
    SimpleGraph.Walk.cons
      (show H.Adj ⟨r, hrootx⟩ ⟨a, hax⟩ from har.symm) q0
  have hreach : H.Reachable ⟨r, hrootx⟩ ⟨d, hdx⟩ := q1.reachable
  have hcompR : H.connectedComponentMk ⟨r, hrootx⟩ = A := by
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff A ⟨r, hrootx⟩).mp
      (by
        simpa only [hrootx] using
          (mem_rootDeletedComponentCarrier_iff G x A r).mp hrA |>.2)
  have hcompD : H.connectedComponentMk ⟨d, hdx⟩ = A := by
    rw [← hcompR]
    exact (SimpleGraph.ConnectedComponent.eq).mpr hreach.symm
  exact (mem_rootDeletedComponentCarrier_iff G x A d).2
    ⟨hdx,
      (SimpleGraph.ConnectedComponent.mem_supp_iff A ⟨d, hdx⟩).mpr hcompD⟩

end Erdos64
