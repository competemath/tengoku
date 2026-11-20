import Tengoku.Erdos64.Erdos64.LeafBlockArticulationDefect
import Tengoku.Erdos64.Erdos64.RootedBranches

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

private noncomputable def rootedBranchCarrier_of_onePort
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (K : Finset V) (root : V)
    (hnonroot : ∃ x, x ∈ K ∧ x ≠ root)
    (hboundary :
      ∀ x, x ∈ K → ∀ y, y ∉ K → G.Adj x y → x = root) :
    RootedBranchCarrier G := by
  classical
  let x := Classical.choose hnonroot
  have hxK : x ∈ K := (Classical.choose_spec hnonroot).1
  have hxroot : x ≠ root := (Classical.choose_spec hnonroot).2
  refine
    { carrier := K.erase root
      root := root
      carrier_nonempty := ⟨x, Finset.mem_erase.mpr ⟨hxroot, hxK⟩⟩
      root_not_mem := by simp
      boundary_root := ?_ }
  intro x hx y hy hxy
  by_cases hyK : y ∈ K
  · by_contra hyr
    exact hy (Finset.mem_erase.mpr ⟨hyr, hyK⟩)
  · have hxK : x ∈ K := (Finset.mem_erase.mp hx).2
    have hxroot : x = root := hboundary x hxK y hyK hxy
    exact ((Finset.mem_erase.mp hx).1 hxroot).elim

/-- In a minimal counterexample, a connected proper one-port carrier has a
    deficient root on the carrier side.  The minimum-degree and criticality
    premises come from the minimal counterexample itself.-/
theorem MinimalCounterexample.connectedOnePortCarrier_internalDegree_le_two
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (K : Finset V) (root : V)
    (hKconn : (G.induce (↑K : Set V)).Connected)
    (hKnonempty : K.Nonempty)
    (hKproper : K ≠ (Finset.univ : Finset V))
    (hroot : root ∈ K)
    (hboundary :
      ∀ x, x ∈ K → ∀ y, y ∉ K → G.Adj x y → x = root) :
    internalDegree G K root ≤ 2 := by
  exact leafBlock_articulation_internalDegree_le_two K root hKconn
    hKnonempty hKproper hroot hboundary
    (fun v _ _ => degree_ge_three_of_minDegree_ge_three G
      M.isCounterexample.1 v)
    M.isSubgraphCritical

/-- At a cubic port, a nontrivial connected one-port carrier has at least one
    root edge on each side.  The two root degrees are both at most two and
    add to three.-/
theorem MinimalCounterexample.connectedOnePortCarrier_cubic_port_degree_split
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (K : Finset V) (root : V)
    (hKconn : (G.induce (↑K : Set V)).Connected)
    (hKnonempty : K.Nonempty)
    (hKproper : K ≠ (Finset.univ : Finset V))
    (hroot : root ∈ K)
    (hnonroot : ∃ x, x ∈ K ∧ x ≠ root)
    (hboundary :
      ∀ x, x ∈ K → ∀ y, y ∉ K → G.Adj x y → x = root)
    (hdegree : G.degree root = 3) :
    1 ≤ (K.filter (G.Adj root)).card ∧
      (K.filter (G.Adj root)).card ≤ 2 ∧
      1 ≤ internalDegree G (Finset.univ \ K.erase root) root ∧
      internalDegree G (Finset.univ \ K.erase root) root ≤ 2 ∧
      internalDegree G (Finset.univ \ K.erase root) root +
          (K.filter (G.Adj root)).card = 3 := by
  classical
  let B := rootedBranchCarrier_of_onePort K root hnonroot hboundary
  have hcarrier_defect : internalDegree G K root ≤ 2 :=
    M.connectedOnePortCarrier_internalDegree_le_two K root hKconn
      hKnonempty hKproper hroot hboundary
  have hsum := B.internalDegree_add_carrierNeighbor_card_eq_degree
  have hfilter :
      (K.erase root).filter (G.Adj root) = K.filter (G.Adj root) := by
    ext x
    by_cases hx : x = root
    · subst x
      simp
    · simp [hx]
  have hsum' :
      internalDegree G (Finset.univ \ K.erase root) root +
          (K.filter (G.Adj root)).card = 3 := by
    change internalDegree G (Finset.univ \ K.erase root) root +
        ((K.erase root).filter (G.Adj root)).card = G.degree root at hsum
    rw [hfilter, hdegree] at hsum
    exact hsum
  have hcomplement_defect :
      internalDegree G (Finset.univ \ K.erase root) root ≤ 2 :=
    by
      exact B.root_internalDegree_le_two M.isSubgraphCritical
        M.isCounterexample.1
  have hcarrier_eq : internalDegree G K root =
      (K.filter (G.Adj root)).card := rfl
  omega

/-- The rooted complement of a nontrivial one-port carrier cannot retain
    minimum degree three.  This is the exact obstruction to closing strict
    induced-subgraph descent from the carrier decomposition.-/
theorem MinimalCounterexample.connectedOnePortCarrier_complement_minDegree_le_two
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (K : Finset V) (root : V)
    (hnonroot : ∃ x, x ∈ K ∧ x ≠ root)
    (hboundary :
      ∀ x, x ∈ K → ∀ y, y ∉ K → G.Adj x y → x = root) :
    (G.induce (↑(Finset.univ \ K.erase root) : Set V)).minDegree ≤ 2 := by
  classical
  let B := rootedBranchCarrier_of_onePort K root hnonroot hboundary
  let vr : (↑(Finset.univ \ K.erase root) : Set V) :=
    ⟨root, Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ root, by simp⟩⟩
  have hroot_degree :
      (G.induce (↑(Finset.univ \ K.erase root) : Set V)).degree vr ≤ 2 := by
    rw [degree_induce_coeFinset_eq_internalDegree G vr]
    exact B.root_internalDegree_le_two M.isSubgraphCritical
      M.isCounterexample.1
  exact le_trans
    ((G.induce (↑(Finset.univ \ K.erase root) : Set V)).minDegree_le_degree vr)
    hroot_degree

end Erdos64
