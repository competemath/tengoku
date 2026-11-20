import Tengoku.Erdos64.Erdos64.RootedBranches

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

set_option maxHeartbeats 800000 in
/-- An actual bridge in a finite minimum-degree-three graph supplies a
strictly small rooted closed side.  The side is chosen from the smaller of
the two endpoint components after deleting the bridge.-/
theorem exists_strict_closed_side_of_bridge
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hconn : G.Connected) (hmin : G.minDegree ≥ 3)
    {u v : V} (huv : G.Adj u v)
    (hbridge : G.IsBridge s(u, v)) :
    ∃ (S : Finset V) (r : {x : V // x ∈ S}),
      (∀ x, x ∈ S → x ≠ r.val →
        ∀ y, G.Adj x y → y ∈ S) ∧
      2 ≤ internalDegree G S r.val ∧
      2 * S.card - 1 < Fintype.card V := by
  classical
  let D : SimpleGraph V := G.deleteEdges {s(u, v)}
  have hnreach : ¬D.Reachable u v := by
    simpa [D] using (SimpleGraph.isBridge_iff.mp hbridge)
  have huv_ne : u ≠ v := huv.ne
  have hside : ∀ {a b : V}, G.Adj a b → s(a, b) = s(u, v) →
      ¬D.Reachable a b →
      ∃ (S : Finset V) (ra : {x : V // x ∈ S}),
        S = (D.connectedComponentMk a).supp.toFinset ∧
        (∀ x, x ∈ S → x ≠ ra.val →
          ∀ y, G.Adj x y → y ∈ S) ∧
        2 ≤ internalDegree G S ra.val := by
    intro a b hab hedge hnab
    let C : D.ConnectedComponent := D.connectedComponentMk a
    let S : Finset V := C.supp.toFinset
    have haS : a ∈ S := by
      apply Set.mem_toFinset.mpr
      simpa [C] using (D.connectedComponentMk_mem a)
    have hbS : b ∉ S := by
      intro hb
      have hb' : b ∈ C.supp := Set.mem_toFinset.mp hb
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hb'
      have hr : D.Reachable b a :=
        (SimpleGraph.ConnectedComponent.eq.mp hb')
      exact hnab hr.symm
    let ra : {x : V // x ∈ S} := ⟨a, haS⟩
    have mem_of_D_adj {x y : V} (hx : x ∈ C.supp)
        (hxy : D.Adj x y) : y ∈ C.supp := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hx ⊢
      rw [← hx]
      exact SimpleGraph.ConnectedComponent.eq.mpr hxy.reachable.symm
    have hdelete_case {x y : V} (hx : x ∈ C.supp)
        (hxroot : x ≠ a) (hxy : G.Adj x y) (hy : y ∉ C.supp) :
        False := by
      have hxyD : D.Adj x y := by
        dsimp [D]
        rw [← hedge]
        apply SimpleGraph.deleteEdges_adj.mpr
        refine ⟨hxy, ?_⟩
        intro he
        have hor : (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
          simpa [Sym2.eq_iff] using he
        rcases hor with hor | hor
        · exact hxroot hor.1
        · exact hy (by
            rw [hor.2]
            simpa [C] using (D.connectedComponentMk_mem a))
      exact hy (mem_of_D_adj hx hxyD)
    have hclosed : ∀ x, x ∈ S → x ≠ ra.val →
        ∀ y, G.Adj x y → y ∈ S := by
      intro x hxS hxroot y hxy
      apply Set.mem_toFinset.mpr
      apply by_contra
      intro hy
      exact hdelete_case (Set.mem_toFinset.mp hxS) hxroot hxy hy
    have houtside : ∀ y, G.Adj a y → y ∉ C.supp → y = b := by
      intro y hay hy
      have hayD : ¬D.Adj a y := by
        intro hayD
        exact hy (mem_of_D_adj (by
          simpa [C] using (D.connectedComponentMk_mem a)) hayD)
      have he : s(a, y) ∈ ({s(a, b)} : Set (Sym2 V)) := by
        by_contra he'
        exact hayD ((show D.Adj a y from by
          dsimp [D]
          rw [← hedge]
          exact SimpleGraph.deleteEdges_adj.mpr ⟨hay, he'⟩))
      have heq : s(a, b) = s(a, y) := (Set.mem_singleton_iff.mp he).symm
      have hor : (a = a ∧ b = y) ∨ (a = y ∧ b = a) := by
        simpa [Sym2.eq_iff] using heq
      rcases hor with hor | hor
      · exact hor.2.symm
      · exact (hab.ne hor.2.symm).elim
    have hneighbors : G.neighborFinset a =
        insert b (S.filter (G.Adj a)) := by
      ext y
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert,
        Finset.mem_filter]
      constructor
      · intro hay
        by_cases hyb : y = b
        · exact Or.inl hyb
        · right
          have hyS : y ∈ C.supp := by
            by_contra hyS
            exact hyb (houtside y hay hyS)
          exact ⟨Set.mem_toFinset.mpr hyS, hay⟩
      · intro hy
        rcases hy with rfl | ⟨hyS, hay⟩
        · exact hab
        · exact hay
    have hrootdeg : 2 ≤ internalDegree G S ra.val := by
      have hcard : G.degree a = 1 + internalDegree G S a := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree, hneighbors]
        have hbnot : b ∉ S.filter (G.Adj a) := by
          intro hb'
          exact hbS (Finset.mem_filter.mp hb').1
        rw [Finset.card_insert_of_notMem hbnot]
        simp [internalDegree, Nat.add_comm]
      have hadeg : 3 ≤ G.degree a :=
        degree_ge_three_of_minDegree_ge_three G hmin a
      simpa [ra] using (show 2 ≤ internalDegree G S a by omega)
    exact ⟨S, ra, rfl, hclosed, hrootdeg⟩
  obtain ⟨S, rS, hS, hSclosed, hSroot⟩ :=
    hside huv rfl hnreach
  obtain ⟨T, rT, hT, hTclosed, hTroot⟩ :=
    hside huv.symm (by simp [Sym2.eq_swap]) (fun h => hnreach h.symm)
  have hdisj : Disjoint S T := by
    rw [hS, hT, Finset.disjoint_left]
    intro z hzS hzT
    have hzS' : z ∈ (D.connectedComponentMk u).supp :=
      Set.mem_toFinset.mp hzS
    have hzT' : z ∈ (D.connectedComponentMk v).supp :=
      Set.mem_toFinset.mp hzT
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hzS' hzT'
    exact hnreach ((SimpleGraph.ConnectedComponent.eq.mp hzS').symm.trans
      (SimpleGraph.ConnectedComponent.eq.mp hzT'))
  have hsum : S.card + T.card ≤ Fintype.card V := by
    have hle : (S ∪ T).card ≤ (Finset.univ : Finset V).card :=
      Finset.card_le_card (Finset.subset_univ _)
    rw [Finset.card_union_of_disjoint hdisj] at hle
    simpa using hle
  have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨rS.val, rS.property⟩
  by_cases hsmall : S.card ≤ T.card
  · refine ⟨S, rS, hSclosed, hSroot, ?_⟩
    omega
  · refine ⟨T, rT, hTclosed, hTroot, ?_⟩
    have hsmall' : T.card ≤ S.card := Nat.le_of_lt (Nat.lt_of_not_ge hsmall)
    omega

end Erdos64
