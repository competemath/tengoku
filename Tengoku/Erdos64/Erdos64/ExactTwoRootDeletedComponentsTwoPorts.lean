import Tengoku.Erdos64.Erdos64.BalancedRootDeletedPartition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- A degree-four root with a two-attachment lower bound on every actual
    root-deleted component has exactly two components, each with two ports,
    once two distinct components are present.
@isnad1 id=ex.3h3v.s8.e0b1746f19dd from=translated src=- shape=c8bc7adb vocab=7cdd21a6
-/
theorem exact_two_rootDeletedComponents_two_ports
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (r : V)
    (hdegree : G.degree r = 4)
    (hports : ∀ C : (G.induce {v : V | v ≠ r}).ConnectedComponent,
      2 ≤ (rootDeletedComponentAttachments G r C).card)
    (hcomponents : ∃ C D : (G.induce {v : V | v ≠ r}).ConnectedComponent,
      C ≠ D) :
    ∃ C D : (G.induce {v : V | v ≠ r}).ConnectedComponent,
      C ≠ D ∧
      (∀ E : (G.induce {v : V | v ≠ r}).ConnectedComponent,
        E = C ∨ E = D) ∧
      (rootDeletedComponentAttachments G r C).card = 2 ∧
      (rootDeletedComponentAttachments G r D).card = 2 := by
  classical
  letI : Fintype ((G.induce {v : V | v ≠ r}).ConnectedComponent) :=
    Fintype.ofFinite _
  obtain ⟨C, D, hCD⟩ := hcomponents
  have hC2 := hports C
  have hD2 := hports D
  have hdisjCD :
      Disjoint (rootDeletedComponentAttachments G r C)
        (rootDeletedComponentAttachments G r D) :=
    (rootDeletedComponentAttachments_pairwise_disjoint r) hCD
  have hsubCD :
      rootDeletedComponentAttachments G r C ∪
          rootDeletedComponentAttachments G r D ⊆ G.neighborFinset r := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_filter.mp hx).1
    · exact (Finset.mem_filter.mp hx).1
  have hCDle :
      (rootDeletedComponentAttachments G r C).card +
          (rootDeletedComponentAttachments G r D).card ≤ 4 := by
    have hunion := Finset.card_union_of_disjoint hdisjCD
    have hle := Finset.card_le_card hsubCD
    rw [hunion] at hle
    simpa [SimpleGraph.card_neighborFinset_eq_degree] using hle.trans_eq hdegree
  have hCeq : (rootDeletedComponentAttachments G r C).card = 2 := by
    omega
  have hDeq : (rootDeletedComponentAttachments G r D).card = 2 := by
    omega
  have honly : ∀ E : (G.induce {v : V | v ≠ r}).ConnectedComponent,
      E = C ∨ E = D := by
    intro E
    by_contra hnot
    have hEC : E ≠ C := by
      intro h
      exact hnot (Or.inl h)
    have hED : E ≠ D := by
      intro h
      exact hnot (Or.inr h)
    have hdisjCE :
        Disjoint (rootDeletedComponentAttachments G r C)
          (rootDeletedComponentAttachments G r E) :=
      (rootDeletedComponentAttachments_pairwise_disjoint r) hEC.symm
    have hdisjDE :
        Disjoint (rootDeletedComponentAttachments G r D)
          (rootDeletedComponentAttachments G r E) :=
      (rootDeletedComponentAttachments_pairwise_disjoint r) hED.symm
    have hdisj_union :
        Disjoint
          (rootDeletedComponentAttachments G r C ∪
            rootDeletedComponentAttachments G r D)
          (rootDeletedComponentAttachments G r E) := by
      apply Finset.disjoint_left.2
      intro x hxCD hxE
      rcases Finset.mem_union.mp hxCD with hxC | hxD
      · exact (Finset.disjoint_left.1 hdisjCE) hxC hxE
      · exact (Finset.disjoint_left.1 hdisjDE) hxD hxE
    have hsub :
        rootDeletedComponentAttachments G r C ∪
            rootDeletedComponentAttachments G r D ∪
            rootDeletedComponentAttachments G r E ⊆ G.neighborFinset r := by
      intro x hx
      rcases Finset.mem_union.mp hx with hxCD | hxE
      · exact hsubCD hxCD
      · exact (Finset.mem_filter.mp hxE).1
    have hle := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj_union,
      Finset.card_union_of_disjoint hdisjCD] at hle
    have hE2 := hports E
    have hdegree' : (G.neighborFinset r).card = 4 := by
      simpa [SimpleGraph.card_neighborFinset_eq_degree] using hdegree
    rw [hdegree'] at hle
    omega
  exact ⟨C, D, hCD, honly, hCeq, hDeq⟩

end Erdos64
