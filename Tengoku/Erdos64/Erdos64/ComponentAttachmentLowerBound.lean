import Tengoku.Erdos64.Erdos64.ComponentAttachments

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Criticality applied to the complement of a root-deleted component forces
    the component to carry almost all of the root's degree.  The first
    conjunct is the connectedness attachment, and the second is the exact
    criticality lower bound on the attachment count.-/
theorem component_attachment_lower_bound
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hconn : G.Connected) (hmin : G.minDegree ≥ 3)
    (hcritical : IsSubgraphCritical G)
    (C : Finset V) (r : V)
    (hCnonempty : C.Nonempty)
    (hrC : r ∉ C)
    (hboundary :
      ∀ x, x ∈ C → ∀ y, y ∉ C → G.Adj x y → y = r) :
    1 ≤ (C.filter (G.Adj r)).card ∧
      G.degree r ≤ (C.filter (G.Adj r)).card + 2 := by
  classical
  let S : Finset V := Finset.univ \ C
  have hrS : r ∈ S := by
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ r, hrC⟩
  have hSnonempty : S.Nonempty := ⟨r, hrS⟩
  have hSproper : S ≠ (Finset.univ : Finset V) := by
    obtain ⟨x, hxC⟩ := hCnonempty
    intro hS
    have hxS : x ∈ S := by
      rw [hS]
      exact Finset.mem_univ x
    exact (Finset.mem_sdiff.mp hxS).2 hxC
  obtain ⟨v, hvS, hvlow⟩ := hcritical S hSnonempty hSproper
  have hvr : v = r := by
    by_contra hvr
    have hneighbors : ∀ w, G.Adj v w → w ∈ S := by
      intro w hvw
      have hwC : w ∉ C := by
        intro hwC
        have hvroot : v = r := hboundary w hwC v
          (Finset.mem_sdiff.mp hvS).2 hvw.symm
        exact hvr hvroot
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hwC⟩
    have hfilter : S.filter (G.Adj v) = G.neighborFinset v := by
      ext w
      constructor
      · intro hw
        exact (G.mem_neighborFinset v w).2
          (Finset.mem_filter.mp hw).2
      · intro hw
        have hvw : G.Adj v w := (G.mem_neighborFinset v w).1 hw
        exact Finset.mem_filter.mpr ⟨hneighbors w hvw, hvw⟩
    have hvinternal : internalDegree G S v = G.degree v := by
      change (S.filter (G.Adj v)).card = G.degree v
      rw [hfilter]
      exact SimpleGraph.card_neighborFinset_eq_degree G v
    rw [hvinternal] at hvlow
    have hvmin : 3 ≤ G.degree v :=
      degree_ge_three_of_minDegree_ge_three G hmin v
    omega
  have hrootlow : internalDegree G S r ≤ 2 := by
    simpa [hvr] using hvlow
  have hunion :
      S.filter (G.Adj r) ∪ C.filter (G.Adj r) = G.neighborFinset r := by
    ext w
    by_cases hwC : w ∈ C
    · simp [S, SimpleGraph.neighborFinset_eq_filter, hwC]
    · simp [S, SimpleGraph.neighborFinset_eq_filter, hwC]
  have hdisjoint :
      Disjoint (S.filter (G.Adj r)) (C.filter (G.Adj r)) := by
    apply Finset.disjoint_left.2
    intro w hwS hwC
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hwS).1).2
      (Finset.mem_filter.mp hwC).1
  have hsum :
      internalDegree G S r + (C.filter (G.Adj r)).card = G.degree r := by
    have hcard := congrArg Finset.card hunion
    rw [Finset.card_union_of_disjoint hdisjoint,
      SimpleGraph.card_neighborFinset_eq_degree] at hcard
    change (S.filter (G.Adj r)).card +
      (C.filter (G.Adj r)).card = G.degree r at hcard
    exact hcard
  have htpos : 1 ≤ (C.filter (G.Adj r)).card := by
    obtain ⟨x, hxC⟩ := hCnonempty
    obtain ⟨u, v, hu, hv, huv⟩ :=
      exists_adj_mem_of_mem_of_not_mem hconn
        (show x ∈ (↑C : Set V) by simpa using hxC)
        (show r ∉ (↑C : Set V) by simpa using hrC)
    have hvr' : v = r := hboundary u (by simpa using hu) v
      (by simpa using hv) huv
    have hur : G.Adj r u := by
      simpa [hvr'] using huv.symm
    have humem : u ∈ C.filter (G.Adj r) :=
      Finset.mem_filter.mpr ⟨by simpa using hu, hur⟩
    exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨u, humem⟩)
  constructor
  · exact htpos
  · omega

end Erdos64
