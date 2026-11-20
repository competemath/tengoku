import Tengoku.Erdos64.Erdos64.RootDeletedBalancedSides
import Tengoku.Erdos64.Erdos64.RootDeletedNestedCarrier

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

private theorem rootDeleted_distinct_carriers_disjoint
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (r : V) (C D : (G.induce {v : V | v ≠ r}).ConnectedComponent)
    (hCD : C ≠ D) :
    Disjoint (rootDeletedComponentCarrier G r C)
      (rootDeletedComponentCarrier G r D) := by
  apply Finset.disjoint_left.mpr
  intro v hvC hvD
  obtain ⟨hvr, hvCs⟩ := (mem_rootDeletedComponentCarrier_iff G r C v).mp hvC
  obtain ⟨_, hvDs⟩ := (mem_rootDeletedComponentCarrier_iff G r D v).mp hvD
  have hC := (SimpleGraph.ConnectedComponent.mem_supp_iff C ⟨v, hvr⟩).mp hvCs
  have hD := (SimpleGraph.ConnectedComponent.mem_supp_iff D ⟨v, hvr⟩).mp hvDs
  exact hCD (hC.symm.trans hD)

/-- Each of the two components at a cut vertex in a minimal counterexample
    has exactly half the vertices other than the cut vertex.-/
theorem MinimalCounterexample.rootDeleted_two_components_order
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (r : V)
    (C D : (G.induce {v : V | v ≠ r}).ConnectedComponent)
    (hCD : C ≠ D) :
    2 * (rootDeletedComponentCarrier G r C).card + 1 = Fintype.card V := by
  obtain ⟨hcard, hcover⟩ := M.rootDeleted_two_components_balanced r C D hCD
  have hroot : r ∉ rootDeletedComponentCarrier G r C ∪
      rootDeletedComponentCarrier G r D := by
    simp only [Finset.mem_union, not_or]
    exact ⟨(rootDeletedComponentCarrier_nonempty_not_mem G r C).2,
      (rootDeletedComponentCarrier_nonempty_not_mem G r D).2⟩
  have htotal := congrArg Finset.card hcover
  rw [Finset.card_insert_of_notMem hroot,
    Finset.card_union_of_disjoint (rootDeleted_distinct_carriers_disjoint r C D hCD),
    Finset.card_univ] at htotal
  omega

/-- A minimal counterexample has at most one cut vertex. If a second cut lay
    in one balanced component of the first, its root-containing component
    would contain the other balanced component and the first root. This is
    strictly more than the size forced by balance at the second cut.

    This theorem does not assert the absence of a cut vertex.-/
theorem MinimalCounterexample.rootDeleted_cut_root_unique
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (r x : V)
    (hr : ∃ C D : (G.induce {v : V | v ≠ r}).ConnectedComponent, C ≠ D)
    (hx : ∃ A B : (G.induce {v : V | v ≠ x}).ConnectedComponent, A ≠ B) :
    r = x := by
  classical
  by_contra hrx
  let A : (G.induce {v : V | v ≠ x}).ConnectedComponent :=
    (G.induce {v : V | v ≠ x}).connectedComponentMk ⟨r, hrx⟩
  have hrA : r ∈ rootDeletedComponentCarrier G x A := by
    apply (mem_rootDeletedComponentCarrier_iff G x A r).mpr
    exact ⟨hrx, (SimpleGraph.ConnectedComponent.mem_supp_iff A ⟨r, hrx⟩).mpr rfl⟩
  obtain ⟨E, F, hEF⟩ := hx
  have hother : ∃ B : (G.induce {v : V | v ≠ x}).ConnectedComponent, A ≠ B := by
    by_cases hAE : A = E
    · exact ⟨F, by simpa only [hAE] using hEF⟩
    · exact ⟨E, hAE⟩
  obtain ⟨B, hAB⟩ := hother
  have hAorder := M.rootDeleted_two_components_order x A B hAB
  have hcontr : ∀ (C D : (G.induce {v : V | v ≠ r}).ConnectedComponent),
      C ≠ D → x ∈ rootDeletedComponentCarrier G r C → False := by
    intro C D hCD hxC
    have hDorder := M.rootDeleted_two_components_order r D C hCD.symm
    have hsubset : insert r (rootDeletedComponentCarrier G r D) ⊆
        rootDeletedComponentCarrier G x A := by
      intro v hv
      rcases Finset.mem_insert.mp hv with hvr | hvD
      · simpa only [hvr] using hrA
      · exact M.rootDeleted_component_nested_in_other_root_component
          r x C D hCD hxC A hrA v hvD
    have hcard := Finset.card_le_card hsubset
    rw [Finset.card_insert_of_notMem
      (rootDeletedComponentCarrier_nonempty_not_mem G r D).2] at hcard
    omega
  obtain ⟨C, D, hCD⟩ := hr
  have hcover := (M.rootDeleted_two_components_balanced r C D hCD).2
  have hxcover : x ∈ insert r (rootDeletedComponentCarrier G r C ∪
      rootDeletedComponentCarrier G r D) := by
    rw [hcover]
    exact Finset.mem_univ x
  rcases Finset.mem_insert.mp hxcover with hxr | hxCD
  · exact hrx hxr.symm
  rcases Finset.mem_union.mp hxCD with hxC | hxD
  · exact hcontr C D hCD hxC
  · exact hcontr D C hCD.symm hxD

/-- Once a cut vertex is present, deleting any other vertex leaves the graph
    connected. The surviving cut vertex also witnesses nonemptiness.-/
theorem MinimalCounterexample.rootDeleted_connected_away_from_cut
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (r x : V)
    (hr : ∃ C D : (G.induce {v : V | v ≠ r}).ConnectedComponent, C ≠ D)
    (hxr : x ≠ r) : (G.induce {v : V | v ≠ x}).Connected := by
  refine { preconnected := ?_, nonempty := ⟨⟨r, hxr.symm⟩⟩ }
  intro u v
  apply SimpleGraph.ConnectedComponent.eq.mp
  by_contra huv
  exact hxr (M.rootDeleted_cut_root_unique r x hr ⟨_, _, huv⟩).symm

end Erdos64
