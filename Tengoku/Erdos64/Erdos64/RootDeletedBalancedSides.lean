import Tengoku.Erdos64.Erdos64.MinimalCounterexampleBalancedSides
import Tengoku.Erdos64.Erdos64.CutVertexComponentBoundary
import Tengoku.Erdos64.Erdos64.CutRootDegreeFour
import Tengoku.Erdos64.Erdos64.RootDeletedTwoPortBalance

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Two distinct components after deleting a vertex already give the balanced
    two-side decomposition.  The component carriers are nonempty, disjoint,
    and have no boundary away from the deleted vertex; minimality then forces
    equal size and exhausts the ambient graph together with the root.-/
theorem MinimalCounterexample.rootDeleted_two_components_balanced
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (r : V)
    (C D : (G.induce {v : V | v ≠ r}).ConnectedComponent)
    (hCD : C ≠ D) :
    (rootDeletedComponentCarrier G r C).card =
        (rootDeletedComponentCarrier G r D).card ∧
      insert r (rootDeletedComponentCarrier G r C ∪
        rootDeletedComponentCarrier G r D) = Finset.univ := by
  have hC := rootDeletedComponentCarrier_nonempty_not_mem G r C
  have hD := rootDeletedComponentCarrier_nonempty_not_mem G r D
  have hdisj :
      Disjoint (rootDeletedComponentCarrier G r C)
        (rootDeletedComponentCarrier G r D) := by
    apply Finset.disjoint_left.mpr
    intro v hvC hvD
    obtain ⟨hvne, hvCsupp⟩ :=
      (mem_rootDeletedComponentCarrier_iff G r C v).1 hvC
    obtain ⟨_, hvDsupp⟩ :=
      (mem_rootDeletedComponentCarrier_iff G r D v).1 hvD
    have hmkC :
        (G.induce {v : V | v ≠ r}).connectedComponentMk ⟨v, hvne⟩ = C :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff C ⟨v, hvne⟩).mp hvCsupp
    have hmkD :
        (G.induce {v : V | v ≠ r}).connectedComponentMk ⟨v, hvne⟩ = D :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff D ⟨v, hvne⟩).mp hvDsupp
    exact hCD (hmkC.symm.trans hmkD)
  have hboundaryC :
      ∀ u, u ∈ rootDeletedComponentCarrier G r C →
        ∀ v, v ∉ rootDeletedComponentCarrier G r C →
          G.Adj u v → v = r := by
    intro u hu v hv huv
    rcases (rootDeletedComponent_boundary r M.isConnected C).1 u hu v huv with
      hvC | hvr
    · exact (hv hvC).elim
    · exact hvr
  have hboundaryD :
      ∀ u, u ∈ rootDeletedComponentCarrier G r D →
        ∀ v, v ∉ rootDeletedComponentCarrier G r D →
          G.Adj u v → v = r := by
    intro u hu v hv huv
    rcases (rootDeletedComponent_boundary r M.isConnected D).1 u hu v huv with
      hvD | hvr
    · exact (hv hvD).elim
    · exact hvr
  exact M.two_onePort_sides_balanced
    (rootDeletedComponentCarrier G r C)
    (rootDeletedComponentCarrier G r D) r
    hC.1 hD.1 hC.2 hD.2 hdisj hboundaryC hboundaryD

/-- The balanced component decomposition also supplies the exact degree-four
    root/two-port interface.  This is the native component form of the
    balanced terminal configuration; it still says nothing about route
    intersections or path lengths.-/
theorem MinimalCounterexample.rootDeleted_two_components_exact_balanced
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (r : V)
    [Fintype ((G.induce {v : V | v ≠ r}).ConnectedComponent)]
    (C D : (G.induce {v : V | v ≠ r}).ConnectedComponent)
    (hCD : C ≠ D) :
    (rootDeletedComponentCarrier G r C).card =
        (rootDeletedComponentCarrier G r D).card ∧
      insert r (rootDeletedComponentCarrier G r C ∪
        rootDeletedComponentCarrier G r D) = Finset.univ ∧
      (rootDeletedComponentAttachments G r C).card = 2 ∧
      (rootDeletedComponentAttachments G r D).card = 2 ∧
      G.degree r = 4 := by
  have hbal := M.rootDeleted_two_components_balanced r C D hCD
  have hC := rootDeletedComponentCarrier_nonempty_not_mem G r C
  have hD := rootDeletedComponentCarrier_nonempty_not_mem G r D
  have hdisj :
      Disjoint (rootDeletedComponentCarrier G r C)
        (rootDeletedComponentCarrier G r D) := by
    apply Finset.disjoint_left.mpr
    intro v hvC hvD
    obtain ⟨hvne, hvCsupp⟩ :=
      (mem_rootDeletedComponentCarrier_iff G r C v).1 hvC
    obtain ⟨_, hvDsupp⟩ :=
      (mem_rootDeletedComponentCarrier_iff G r D v).1 hvD
    have hmkC :
        (G.induce {v : V | v ≠ r}).connectedComponentMk ⟨v, hvne⟩ = C :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff C ⟨v, hvne⟩).mp hvCsupp
    have hmkD :
        (G.induce {v : V | v ≠ r}).connectedComponentMk ⟨v, hvne⟩ = D :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff D ⟨v, hvne⟩).mp hvDsupp
    exact hCD (hmkC.symm.trans hmkD)
  have hboundaryC :
      ∀ u, u ∈ rootDeletedComponentCarrier G r C →
        ∀ v, v ∉ rootDeletedComponentCarrier G r C →
          G.Adj u v → v = r := by
    intro u hu v hv huv
    rcases (rootDeletedComponent_boundary r M.isConnected C).1 u hu v huv with
      hvC | hvr
    · exact (hv hvC).elim
    · exact hvr
  have hboundaryD :
      ∀ u, u ∈ rootDeletedComponentCarrier G r D →
        ∀ v, v ∉ rootDeletedComponentCarrier G r D →
          G.Adj u v → v = r := by
    intro u hu v hv huv
    rcases (rootDeletedComponent_boundary r M.isConnected D).1 u hu v huv with
      hvD | hvr
    · exact (hv hvD).elim
    · exact hvr
  have hdegree := two_closed_sides_root_degree_four M
    (rootDeletedComponentCarrier G r C)
    (rootDeletedComponentCarrier G r D) r
    hC.1 hD.1 hC.2 hD.2 hdisj hbal.2 hboundaryC hboundaryD
  have hattachC :
      rootDeletedComponentAttachments G r C =
        (rootDeletedComponentCarrier G r C).filter (G.Adj r) := by
    ext v
    simp [rootDeletedComponentAttachments,
      SimpleGraph.neighborFinset_eq_filter, and_comm]
  have hattachD :
      rootDeletedComponentAttachments G r D =
        (rootDeletedComponentCarrier G r D).filter (G.Adj r) := by
    ext v
    simp [rootDeletedComponentAttachments,
      SimpleGraph.neighborFinset_eq_filter, and_comm]
  refine ⟨hbal.1, hbal.2, ?_, ?_, hdegree.2.2⟩
  · rw [hattachC]
    exact hdegree.1
  · rw [hattachD]
    exact hdegree.2.1

/-- Edge-minimality upgrades the exact balanced component decomposition to the
    cubic-port conclusion used by the terminal case split.-/
theorem EdgeMinimalCounterexample.rootDeleted_two_components_exact_balanced_cubic
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : EdgeMinimalCounterexample G) (r : V)
    [Fintype ((G.induce {v : V | v ≠ r}).ConnectedComponent)]
    (C D : (G.induce {v : V | v ≠ r}).ConnectedComponent)
    (hCD : C ≠ D) :
    (rootDeletedComponentCarrier G r C).card =
        (rootDeletedComponentCarrier G r D).card ∧
      insert r (rootDeletedComponentCarrier G r C ∪
        rootDeletedComponentCarrier G r D) = Finset.univ ∧
      (rootDeletedComponentAttachments G r C).card = 2 ∧
      (rootDeletedComponentAttachments G r D).card = 2 ∧
      G.degree r = 4 ∧
      (∀ v, G.Adj r v → G.degree v = 3) := by
  obtain ⟨hcard, hcover, hCports, hDports, hdegree⟩ :=
    M.vertexMinimal.rootDeleted_two_components_exact_balanced r C D hCD
  have hcubic : ∀ v, G.Adj r v → G.degree v = 3 := by
    intro v hrv
    exact M.neighbor_degree_eq_three_of_degree_ge_four (by omega) hrv
  exact ⟨hcard, hcover, hCports, hDports, hdegree, hcubic⟩

/-- The same certificate rules out a third component of `G - {r}`.-/
theorem MinimalCounterexample.rootDeleted_two_components_exactly
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (r : V)
    [Fintype ((G.induce {v : V | v ≠ r}).ConnectedComponent)]
    (C D : (G.induce {v : V | v ≠ r}).ConnectedComponent)
    (hCD : C ≠ D) :
    (rootDeletedComponentCarrier G r C).card =
        (rootDeletedComponentCarrier G r D).card ∧
      insert r (rootDeletedComponentCarrier G r C ∪
        rootDeletedComponentCarrier G r D) = Finset.univ ∧
      (rootDeletedComponentAttachments G r C).card = 2 ∧
      (rootDeletedComponentAttachments G r D).card = 2 ∧
      G.degree r = 4 ∧
      (∀ E : (G.induce {v : V | v ≠ r}).ConnectedComponent,
        E = C ∨ E = D) := by
  obtain ⟨hcard, hcover, hCports, hDports, hdegree⟩ :=
    M.rootDeleted_two_components_exact_balanced r C D hCD
  have honly :
      ∀ E : (G.induce {v : V | v ≠ r}).ConnectedComponent,
        E = C ∨ E = D := by
    intro E
    obtain ⟨v, hv⟩ :=
      (rootDeletedComponentCarrier_nonempty_not_mem G r E).1
    have hvr : v ≠ r := by
      intro hvr
      subst v
      exact (rootDeletedComponentCarrier_nonempty_not_mem G r E).2 hv
    have hvcover :
        v ∈ insert r (rootDeletedComponentCarrier G r C ∪
          rootDeletedComponentCarrier G r D) := by
      rw [hcover]
      exact Finset.mem_univ v
    have hvCD : v ∈
        rootDeletedComponentCarrier G r C ∪
          rootDeletedComponentCarrier G r D := by
      rcases Finset.mem_insert.mp hvcover with hroot | hvCD
      · exact (hvr hroot).elim
      · exact hvCD
    rcases Finset.mem_union.mp hvCD with hvC | hvD
    · left
      obtain ⟨hvne, hvEsupp⟩ :=
        (mem_rootDeletedComponentCarrier_iff G r E v).1 hv
      obtain ⟨_, hvCsupp⟩ :=
        (mem_rootDeletedComponentCarrier_iff G r C v).1 hvC
      have hmkE :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff E ⟨v, hvne⟩).mp hvEsupp
      have hmkC :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff C ⟨v, hvne⟩).mp hvCsupp
      exact hmkE.symm.trans hmkC
    · right
      obtain ⟨hvne, hvEsupp⟩ :=
        (mem_rootDeletedComponentCarrier_iff G r E v).1 hv
      obtain ⟨_, hvDsupp⟩ :=
        (mem_rootDeletedComponentCarrier_iff G r D v).1 hvD
      have hmkE :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff E ⟨v, hvne⟩).mp hvEsupp
      have hmkD :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff D ⟨v, hvne⟩).mp hvDsupp
      exact hmkE.symm.trans hmkD
  exact ⟨hcard, hcover, hCports, hDports, hdegree, honly⟩

end Erdos64
