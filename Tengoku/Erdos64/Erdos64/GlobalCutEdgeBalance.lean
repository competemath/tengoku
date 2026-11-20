import Tengoku.Erdos64.Erdos64.GlobalEdgeMinimalCounterexample
import Tengoku.Erdos64.Erdos64.RootedDoubleEdgeCount
import Tengoku.Erdos64.Erdos64.ClosedSideEdgeCount
import Tengoku.Erdos64.Erdos64.EqualCutRootBalancedExcess
import Tengoku.Erdos64.Erdos64.RootDeletedBalancedSides

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- At a globally edge-minimal counterexample, equally sized closed sides
meeting at one root have equal edge counts. Each balanced double is a
same-order counterexample, so both edge-count comparisons are justified.
The sides include the root and all of their root-attachment edges.-/
theorem GlobalEdgeMinimalCounterexample.closed_sides_edge_count_eq
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : GlobalEdgeMinimalCounterexample G)
    (A B : Finset V) (r : V)
    (hpartition : A ∪ B = Finset.univ)
    (hinter : A ∩ B = {r})
    (hclosedA : ∀ x, x ∈ A → x ≠ r → ∀ y, G.Adj x y → y ∈ A)
    (hclosedB : ∀ x, x ∈ B → x ≠ r → ∀ y, G.Adj x y → y ∈ B)
    (hrootA : 2 ≤ internalDegree G A r)
    (hrootB : 2 ≤ internalDegree G B r)
    (hcard : A.card = B.card) :
    (G.induce (↑A : Set V)).edgeFinset.card =
      (G.induce (↑B : Set V)).edgeFinset.card := by
  classical
  have hr : r ∈ A ∧ r ∈ B := by
    apply Finset.mem_inter.mp
    rw [hinter]
    simp
  have horder := Finset.card_union_add_card_inter A B
  rw [hpartition, hinter, Finset.card_univ, Finset.card_singleton] at horder
  have hcompare : ∀ (S : Finset V) (hS : r ∈ S),
      (∀ x, x ∈ S → x ≠ r → ∀ y, G.Adj x y → y ∈ S) →
      2 ≤ internalDegree G S r → S.card = A.card →
      G.edgeFinset.card ≤ 2 * (G.induce (↑S : Set V)).edgeFinset.card := by
    intro S hS hclosed hroot hScard
    let root : {v : V // v ∈ S} := ⟨r, hS⟩
    have hcounter := rootedDouble_closed_side_isCounterexample
      M.vertexMinimal.isCounterexample S root hclosed hroot
    have hsize : Fintype.card (RootedDoubleVertex (↑S : Set V) root) =
        Fintype.card V := by
      rw [rootedDouble_card]
      have hSsize : Fintype.card (↑S : Set V) = S.card :=
        Fintype.card_of_finset' S (fun _ => Iff.rfl)
      rw [hSsize]
      omega
    have hle := M.edgeCountMinimal _ _ hcounter hsize
    rw [rootedDouble_edgeSet_ncard] at hle
    simpa only [Set.ncard_eq_toFinset_card', SimpleGraph.edgeFinset] using hle
  have hA := hcompare A hr.1 hclosedA hrootA rfl
  have hB := hcompare B hr.2 hclosedB hrootB hcard.symm
  have hsum := closed_sides_edge_count A B r hpartition hinter hclosedA hclosedB
  omega

/-- Native one-port sides of a globally edge-minimal counterexample have
equal edge counts and equal nonroot degree excess. Balance, the two root
attachments, and the edge-count equality are all produced here. Equal excess
does not imply zero excess or cubicity of every side vertex.-/
theorem GlobalEdgeMinimalCounterexample.two_onePort_sides_balanced_edges_excess
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : GlobalEdgeMinimalCounterexample G)
    (D E : Finset V) (r : V)
    (hD : D.Nonempty) (hE : E.Nonempty)
    (hrD : r ∉ D) (hrE : r ∉ E)
    (hdisj : Disjoint D E)
    (hboundaryD : ∀ u, u ∈ D → ∀ v, v ∉ D → G.Adj u v → v = r)
    (hboundaryE : ∀ u, u ∈ E → ∀ v, v ∉ E → G.Adj u v → v = r) :
    (G.induce (↑(insert r D) : Set V)).edgeFinset.card =
        (G.induce (↑(insert r E) : Set V)).edgeFinset.card ∧
      nonrootDegreeExcess G (insert r D) r =
        nonrootDegreeExcess G (insert r E) r := by
  classical
  obtain ⟨hcard, hcover⟩ := M.vertexMinimal.two_onePort_sides_balanced
    D E r hD hE hrD hrE hdisj hboundaryD hboundaryE
  obtain ⟨hdegreeD, hdegreeE, _⟩ := M.vertexMinimal.two_closed_sides_root_degree_four
    D E r hD hE hrD hrE hdisj hcover hboundaryD hboundaryE
  let A := insert r D
  let B := insert r E
  have hrootA : r ∈ A := Finset.mem_insert_self r D
  have hrootB : r ∈ B := Finset.mem_insert_self r E
  have hpartition : A ∪ B = Finset.univ := by
    simpa only [A, B, Finset.insert_union, Finset.union_insert, Finset.insert_idem]
      using hcover
  have hinter : A ∩ B = {r} := by
    ext v
    simp only [A, B, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hvD, hvE⟩
      rcases hvD with hvr | hvD
      · exact hvr
      rcases hvE with hvr | hvE
      · exact hvr
      exact ((Finset.disjoint_left.mp hdisj) hvD hvE).elim
    · intro hvr
      exact ⟨Or.inl hvr, Or.inl hvr⟩
  have closed : ∀ K : Finset V,
      (∀ u, u ∈ K → ∀ v, v ∉ K → G.Adj u v → v = r) →
      ∀ u, u ∈ insert r K → u ≠ r → ∀ v, G.Adj u v → v ∈ insert r K := by
    intro K hboundary u hu hur v huv
    have huK := (Finset.mem_insert.mp hu).resolve_left hur
    by_cases hvK : v ∈ K
    · exact Finset.mem_insert.mpr (Or.inr hvK)
    · exact Finset.mem_insert.mpr (Or.inl (hboundary u huK v hvK huv))
  have hclosedA := closed D hboundaryD
  have hclosedB := closed E hboundaryE
  have hrootDegreeA : 2 ≤ internalDegree G A r := by
    have heq : internalDegree G A r = 2 := by
      simpa [A, internalDegree, Finset.filter_insert] using hdegreeD
    omega
  have hrootDegreeB : 2 ≤ internalDegree G B r := by
    have heq : internalDegree G B r = 2 := by
      simpa [B, internalDegree, Finset.filter_insert] using hdegreeE
    omega
  have hcardAB : A.card = B.card := by
    simp only [A, B, Finset.card_insert_of_notMem hrD,
      Finset.card_insert_of_notMem hrE, hcard]
  have hedges := M.closed_sides_edge_count_eq A B r hpartition hinter
    hclosedA hclosedB hrootDegreeA hrootDegreeB hcardAB
  have hnocross : ∀ x, x ∈ A → x ≠ r →
      ∀ y, y ∈ B → y ≠ r → ¬ G.Adj x y := by
    intro x hx hxr y hy hyr hxy
    have hyA := hclosedA x hx hxr y hxy
    have hyAB := Finset.mem_inter.mpr ⟨hyA, hy⟩
    rw [hinter, Finset.mem_singleton] at hyAB
    exact hyr hyAB
  have hbalance := equal_cut_root_balanced_excess M.toEdgeMinimalCounterexample
    A B r hpartition hinter hrootA hrootB hclosedA hclosedB hnocross
    hrootDegreeA hrootDegreeB hcardAB hedges
  exact ⟨hedges, hbalance.2.2.2.2⟩

/-- Any two distinct actual components at a cut root have equal closed-side
edge counts and equal nonroot degree excess under global edge-count minimality.
No independent side-cardinality, attachment, or edge-balance premise remains.-/
theorem GlobalEdgeMinimalCounterexample.rootDeleted_two_components_balanced_edges_excess
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : GlobalEdgeMinimalCounterexample G) (r : V)
    (C D : (G.induce {v : V | v ≠ r}).ConnectedComponent)
    (hCD : C ≠ D) :
    (G.induce (↑(insert r (rootDeletedComponentCarrier G r C)) : Set V)).edgeFinset.card =
        (G.induce (↑(insert r (rootDeletedComponentCarrier G r D)) : Set V)).edgeFinset.card ∧
      nonrootDegreeExcess G (insert r (rootDeletedComponentCarrier G r C)) r =
        nonrootDegreeExcess G (insert r (rootDeletedComponentCarrier G r D)) r := by
  have hC := rootDeletedComponentCarrier_nonempty_not_mem G r C
  have hD := rootDeletedComponentCarrier_nonempty_not_mem G r D
  have hdisj : Disjoint (rootDeletedComponentCarrier G r C)
      (rootDeletedComponentCarrier G r D) := by
    apply Finset.disjoint_left.mpr
    intro v hvC hvD
    obtain ⟨hvr, hvCs⟩ := (mem_rootDeletedComponentCarrier_iff G r C v).mp hvC
    obtain ⟨_, hvDs⟩ := (mem_rootDeletedComponentCarrier_iff G r D v).mp hvD
    have hmkC := (SimpleGraph.ConnectedComponent.mem_supp_iff C ⟨v, hvr⟩).mp hvCs
    have hmkD := (SimpleGraph.ConnectedComponent.mem_supp_iff D ⟨v, hvr⟩).mp hvDs
    exact hCD (hmkC.symm.trans hmkD)
  have boundary : ∀ E : (G.induce {v : V | v ≠ r}).ConnectedComponent,
      ∀ u, u ∈ rootDeletedComponentCarrier G r E →
        ∀ v, v ∉ rootDeletedComponentCarrier G r E → G.Adj u v → v = r := by
    intro E u hu v hv huv
    rcases (rootDeletedComponent_boundary r M.vertexMinimal.isConnected E).1
        u hu v huv with hvE | hvr
    · exact (hv hvE).elim
    · exact hvr
  exact M.two_onePort_sides_balanced_edges_excess
    (rootDeletedComponentCarrier G r C) (rootDeletedComponentCarrier G r D)
    r hC.1 hD.1 hC.2 hD.2 hdisj (boundary C) (boundary D)

end Erdos64
