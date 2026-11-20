import Tengoku.Erdos64.Erdos64.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Degree in an induced finite vertex set is the ambient internal degree.
@isnad1 id=eq.0h4v.s8.ec174b95ce3b from=translated src=- shape=6f73df59 vocab=184c5d92
-/
theorem degree_induce_coeFinset_eq_internalDegree
    {V : Type u} (G : SimpleGraph V) [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj]
    {S : Finset V} (v : (↑S : Set V)) :
    (G.induce (↑S : Set V)).degree v = internalDegree G S v.1 := by
  classical
  change ((G.induce (↑S : Set V)).neighborFinset v).card =
    (S.filter (G.Adj v.1)).card
  have hfin :
      (((G.induce (↑S : Set V)).neighborFinset v).map
          (.subtype (· ∈ (↑S : Set V)))) =
        G.neighborFinset v ∩ (↑S : Set V).toFinset := by
    ext w
    simp [SimpleGraph.neighborFinset_eq_filter]
  have hcardmap := congrArg Finset.card hfin
  have hinter :
      G.neighborFinset v ∩ (↑S : Set V).toFinset =
        S.filter (G.Adj v.1) := by
    ext w
    simp [SimpleGraph.neighborFinset_eq_filter, and_comm]
  calc
    ((G.induce (↑S : Set V)).neighborFinset v).card =
        (((G.induce (↑S : Set V)).neighborFinset v).map
          (.subtype (· ∈ (↑S : Set V)))).card := by
            rw [Finset.card_map]
    _ = (G.neighborFinset v ∩ (↑S : Set V).toFinset).card := hcardmap
    _ = (S.filter (G.Adj v.1)).card := congrArg Finset.card hinter

/-- A nonempty finite carrier whose boundary edges end at an external root.
No degree preservation at the root is part of this record.-/
structure RootedBranchCarrier {V : Type u} (G : SimpleGraph V) where
  carrier : Finset V
  root : V
  carrier_nonempty : carrier.Nonempty
  root_not_mem : root ∉ carrier
  boundary_root :
    ∀ x, x ∈ carrier → ∀ y, y ∉ carrier → G.Adj x y → y = root

namespace RootedBranchCarrier

variable {V : Type u} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Removing the carrier loses no neighbors at a retained vertex other than the root.
@isnad1 id=eq.2h4v.s6.0aa6d5011ade from=translated src=- shape=76246093 vocab=b1c040be
-/
theorem internalDegree_compl_eq_degree_of_ne_root
    (B : RootedBranchCarrier G) {v : V}
    (hv : v ∉ B.carrier) (hvroot : v ≠ B.root) :
    internalDegree G (Finset.univ \ B.carrier) v = G.degree v := by
  classical
  have hfin :
      (Finset.univ \ B.carrier).filter (G.Adj v) = G.neighborFinset v := by
    ext w
    constructor
    · intro hw
      exact (G.mem_neighborFinset v w).2 (Finset.mem_filter.mp hw).2
    · intro hw
      have hvw : G.Adj v w := (G.mem_neighborFinset v w).1 hw
      refine Finset.mem_filter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, ?_⟩, hvw⟩
      intro hwK
      exact hvroot (B.boundary_root w hwK v hv hvw.symm)
  change ((Finset.univ \ B.carrier).filter (G.Adj v)).card = G.degree v
  rw [hfin]
  exact SimpleGraph.card_neighborFinset_eq_degree G v

/-- The induced complement preserves degrees away from the root.
@isnad1 id=eq.1h4v.s9.3e1eafd57795 from=translated src=- shape=5063d579 vocab=3c012b48
-/
theorem degree_induce_compl_eq_degree_of_ne_root
    (B : RootedBranchCarrier G)
    (v : (↑(Finset.univ \ B.carrier) : Set V))
    (hvroot : v.1 ≠ B.root) :
    (G.induce (↑(Finset.univ \ B.carrier) : Set V)).degree v =
      G.degree v.1 := by
  rw [degree_induce_coeFinset_eq_internalDegree G v]
  exact B.internalDegree_compl_eq_degree_of_ne_root
    (Finset.mem_sdiff.mp v.2).2 hvroot

/-- In a critical graph of minimum degree at least three, the root is the
deficient vertex of the proper nonempty induced complement.
@isnad1 id=le.2h3v.s6.9004df40aa07 from=translated src=- shape=0412f778 vocab=64dfc765
-/
theorem root_internalDegree_le_two
    (B : RootedBranchCarrier G)
    (hcritical : IsSubgraphCritical G) (hmin : G.minDegree ≥ 3) :
    internalDegree G (Finset.univ \ B.carrier) B.root ≤ 2 := by
  classical
  have hS_nonempty : (Finset.univ \ B.carrier).Nonempty :=
    ⟨B.root, Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ B.root, B.root_not_mem⟩⟩
  have hS_proper : Finset.univ \ B.carrier ≠ (Finset.univ : Finset V) := by
    intro hS
    obtain ⟨x, hx⟩ := B.carrier_nonempty
    have hxS : x ∈ Finset.univ \ B.carrier := by
      rw [hS]
      exact Finset.mem_univ x
    exact (Finset.mem_sdiff.mp hxS).2 hx
  obtain ⟨v, hv, hvlow⟩ := hcritical _ hS_nonempty hS_proper
  by_cases hvroot : v = B.root
  · simpa only [hvroot] using hvlow
  · have heq := B.internalDegree_compl_eq_degree_of_ne_root
      (Finset.mem_sdiff.mp hv).2 hvroot
    have hvmin : 3 ≤ G.degree v :=
      degree_ge_three_of_minDegree_ge_three G hmin v
    rw [heq] at hvlow
    omega

/-- The neighbors of the root split between the retained complement and the
carrier.
@isnad1 id=eq.0h3v.s6.ee033be6b12f from=translated src=- shape=1b140d61 vocab=33ad559f
-/
theorem internalDegree_add_carrierNeighbor_card_eq_degree
    (B : RootedBranchCarrier G) :
    internalDegree G (Finset.univ \ B.carrier) B.root +
        (B.carrier.filter (G.Adj B.root)).card = G.degree B.root := by
  classical
  have hunion :
      (Finset.univ \ B.carrier).filter (G.Adj B.root) ∪
          B.carrier.filter (G.Adj B.root) = G.neighborFinset B.root := by
    ext w
    by_cases hw : w ∈ B.carrier <;>
      simp [SimpleGraph.neighborFinset_eq_filter, hw]
  have hdisjoint :
      Disjoint ((Finset.univ \ B.carrier).filter (G.Adj B.root))
        (B.carrier.filter (G.Adj B.root)) := by
    apply Finset.disjoint_left.2
    intro w hwS hwK
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hwS).1).2
      (Finset.mem_filter.mp hwK).1
  have hcard := congrArg Finset.card hunion
  rw [Finset.card_union_of_disjoint hdisjoint,
    SimpleGraph.card_neighborFinset_eq_degree] at hcard
  exact hcard

/-- A degree-three root with at most two retained neighbors has a carrier
neighbor.
@isnad1 id=ex.2h3v.s6.6d16c3fb776d from=translated src=- shape=4f470d29 vocab=08b300dd
-/
theorem exists_carrier_neighbor_of_degree_eq_three_of_root_internalDegree_le_two
    (B : RootedBranchCarrier G)
    (hdeg : G.degree B.root = 3)
    (hroot : internalDegree G (Finset.univ \ B.carrier) B.root ≤ 2) :
    ∃ w, w ∈ B.carrier ∧ G.Adj B.root w := by
  have hsum := B.internalDegree_add_carrierNeighbor_card_eq_degree
  rw [hdeg] at hsum
  have hpositive :
      0 < (B.carrier.filter (G.Adj B.root)).card := by
    omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpositive
  exact ⟨w, (Finset.mem_filter.mp hw).1, (Finset.mem_filter.mp hw).2⟩

/-- In the same situation, the carrier boundary-neighbor count is between one
and three, with the exact sum given by the preceding partition theorem.
@isnad1 id=and.2h3v.s7.62338c81b738 from=translated src=- shape=4a6ced01 vocab=34636c05
-/
theorem one_le_carrierNeighbor_card_of_degree_eq_three_of_root_internalDegree_le_two
    (B : RootedBranchCarrier G)
    (hdeg : G.degree B.root = 3)
    (hroot : internalDegree G (Finset.univ \ B.carrier) B.root ≤ 2) :
    1 ≤ (B.carrier.filter (G.Adj B.root)).card ∧
      (B.carrier.filter (G.Adj B.root)).card ≤ 3 := by
  have hsum := B.internalDegree_add_carrierNeighbor_card_eq_degree
  rw [hdeg] at hsum
  omega

/-- The obstruction obtained from subgraph criticality at a degree-three root.
@isnad1 id=ex.3h3v.s6.5918b821e517 from=translated src=- shape=d1fa1e23 vocab=742f4106
-/
theorem exists_carrier_neighbor_of_degree_eq_three
    (B : RootedBranchCarrier G)
    (hcritical : IsSubgraphCritical G) (hmin : G.minDegree ≥ 3)
    (hdeg : G.degree B.root = 3) :
    ∃ w, w ∈ B.carrier ∧ G.Adj B.root w :=
  B.exists_carrier_neighbor_of_degree_eq_three_of_root_internalDegree_le_two
    hdeg (B.root_internalDegree_le_two hcritical hmin)

/-- Complement minimum degree is conditional on the root retaining three neighbors.
@isnad1 id=le.2h3v.s8.1692cd5193cf from=translated src=- shape=4b95f65c vocab=83a4b0fa
-/
theorem complement_minDegree_ge_three
    (B : RootedBranchCarrier G) (hmin : G.minDegree ≥ 3)
    (hroot : 3 ≤ internalDegree G (Finset.univ \ B.carrier) B.root) :
    (G.induce (↑(Finset.univ \ B.carrier) : Set V)).minDegree ≥ 3 := by
  classical
  letI : Nonempty (↑(Finset.univ \ B.carrier) : Set V) :=
    ⟨⟨B.root, Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ B.root, B.root_not_mem⟩⟩⟩
  apply SimpleGraph.le_minDegree_of_forall_le_degree
    (G := G.induce (↑(Finset.univ \ B.carrier) : Set V)) 3
  intro v
  rw [degree_induce_coeFinset_eq_internalDegree G v]
  by_cases hvroot : v.1 = B.root
  · simpa only [hvroot] using hroot
  · rw [B.internalDegree_compl_eq_degree_of_ne_root
      (Finset.mem_sdiff.mp v.2).2 hvroot]
    exact degree_ge_three_of_minDegree_ge_three G hmin v.1

/-- A nonempty carrier makes its induced complement strictly smaller.
@isnad1 id=lt.0h3v.s6.fdf93c4444a8 from=translated src=- shape=fd183601 vocab=594a0186
-/
theorem complement_card_lt (B : RootedBranchCarrier G) :
    Fintype.card (↑(Finset.univ \ B.carrier) : Set V) < Fintype.card V := by
  classical
  obtain ⟨x, hx⟩ := B.carrier_nonempty
  have hxnot : x ∉ (↑(Finset.univ \ B.carrier) : Set V) := by
    intro hxS
    exact (Finset.mem_sdiff.mp hxS).2 hx
  exact Fintype.card_subtype_lt hxnot

/-- Conditional induced-subgraph descent: the residual degree at the root
must be supplied separately from the boundary conditions.
@isnad1 id=isstrict.2h3v.s8.5352bb70c977 from=translated src=- shape=2514d38c vocab=886ee273
-/
theorem isStrictlySmallerCounterexample_compl
    (B : RootedBranchCarrier G) (hcounter : IsCounterexample G)
    (hroot : 3 ≤ internalDegree G (Finset.univ \ B.carrier) B.root) :
    IsStrictlySmallerCounterexample G
      (G.induce (↑(Finset.univ \ B.carrier) : Set V)) := by
  classical
  refine ⟨⟨B.complement_minDegree_ge_three hcounter.1 hroot, ?_⟩,
    B.complement_card_lt⟩
  intro hpow
  rcases hpow with ⟨k, v, c, hk, hc, hlen⟩
  let e := (SimpleGraph.Embedding.induce (G := G)
    (s := (↑(Finset.univ \ B.carrier) : Set V))).toHom
  refine hcounter.2 ⟨k, e v, c.map e, hk, ?_, ?_⟩
  · exact hc.map Subtype.val_injective
  · exact (SimpleGraph.Walk.length_map e c).trans hlen

/-- Cycle vertices that have a neighbor in an external finite carrier.-/
def attachmentSet (G : SimpleGraph V) [DecidableRel G.Adj]
    (C K : Finset V) : Finset V :=
  C.filter (fun a => (K.filter (G.Adj a)).Nonempty)

/-- A nonempty finite attachment set either has two distinct members or is a
singleton. This uses no connectivity or degree assumption.
@isnad1 id=or.1h4v.s6.829426bba90c from=translated src=- shape=8133212b vocab=8e44b250
-/
theorem attachmentSet_two_or_singleton
    {C K : Finset V}
    (hattach : (attachmentSet G C K).Nonempty) :
    (∃ a b, a ∈ attachmentSet G C K ∧
      b ∈ attachmentSet G C K ∧ a ≠ b) ∨
    ∃ r, attachmentSet G C K = {r} := by
  by_cases htwo : ∃ a b, a ∈ attachmentSet G C K ∧
      b ∈ attachmentSet G C K ∧ a ≠ b
  · exact Or.inl htwo
  · right
    obtain ⟨r, hr⟩ := hattach
    refine ⟨r, ?_⟩
    ext a
    constructor
    · intro ha
      have har : a = r := by
        by_contra hne
        exact htwo ⟨a, r, ha, hr, hne⟩
      exact Finset.mem_singleton.mpr har
    · intro ha
      rw [Finset.mem_singleton] at ha
      simpa [ha] using hr

/-- The singleton-attachment branch yields the rooted carrier abstraction
when the external carrier is separated from the rest of the graph.-/
def rootedBranchCarrier_of_singleton_attachment
    {C K : Finset V} {r : V}
    (hK : K.Nonempty) (hrC : r ∈ C) (hdisjoint : Disjoint C K)
    (hseparated :
      ∀ x, x ∉ C → x ∉ K →
        ∀ y, y ∈ K → ¬G.Adj x y)
    (hsingleton : attachmentSet G C K = {r}) :
    RootedBranchCarrier G := by
  have hrK : r ∉ K := (Finset.disjoint_left.mp hdisjoint) hrC
  refine
    { carrier := K
      root := r
      carrier_nonempty := hK
      root_not_mem := hrK
      boundary_root := ?_ }
  intro x hxK y hyK hxy
  by_cases hyC : y ∈ C
  · have hyatt : y ∈ attachmentSet G C K := by
      unfold attachmentSet
      apply Finset.mem_filter.mpr
      refine ⟨hyC, ?_⟩
      exact ⟨x, Finset.mem_filter.mpr ⟨hxK, hxy.symm⟩⟩
    rw [hsingleton] at hyatt
    exact Finset.mem_singleton.mp hyatt
  · exact (hseparated y hyC hyK x hxK) hxy.symm |>.elim

end RootedBranchCarrier

end Erdos64
