import Tengoku.Erdos64.Erdos64.AdjacentTwoPortThirdNeighbors

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

open scoped Classical

/-- The ambient carrier of a component of the two-port-deleted induced graph.-/
noncomputable def separatedThirdNeighborComponentCarrier
    {V : Type u} (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    (D : Finset V) (x y : V)
    (C : (G.induce (↑(D.erase x |>.erase y) : Set V)).ConnectedComponent) :
    Finset V := by
  classical
  letI : Fintype C := Fintype.ofFinite _
  exact C.supp.toFinset.image Subtype.val

theorem separatedThirdNeighborComponentCarrier_mem_iff
    {V : Type u} (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    (D : Finset V) (x y : V)
    (C : (G.induce (↑(D.erase x |>.erase y) : Set V)).ConnectedComponent)
    (v : V) :
    v ∈ separatedThirdNeighborComponentCarrier G D x y C ↔
      ∃ hv : v ∈ (D.erase x |>.erase y),
        (⟨v, (show v ∈ (↑(D.erase x |>.erase y) : Set V) from hv)⟩ :
          (↑(D.erase x |>.erase y) : Set V)) ∈ C.supp := by
  classical
  simp [separatedThirdNeighborComponentCarrier]

/-- In the adjacent cubic two-port configuration, separated third neighbors
    either belong to one component after deleting the two ports, or the
    component containing `z` is a proper one-port leaf carrier rooted at `x`.

    This is a structural split only; it makes no global cycle claim.-/
theorem separated_third_neighbor_component_split
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (D : Finset V) (r x y z w : V)
    (hr : r ∉ D)
    (hports : x ∈ D ∧ y ∈ D ∧ x ≠ y)
    (hboundary :
      ∀ v, v ∈ D → ∀ t, t ∉ D → G.Adj v t → t = r)
    (hexact :
      ∀ v, v ∈ D → (G.Adj v r ↔ v = x ∨ v = y))
    (hcubic : G.degree x = 3 ∧ G.degree y = 3)
    (hxy : G.Adj x y)
    (hz : z ∈ D ∧ z ≠ r ∧ z ≠ x ∧ z ≠ y ∧ G.Adj x z)
    (hw : w ∈ D ∧ w ≠ r ∧ w ≠ x ∧ w ≠ y ∧ G.Adj y w)
    (hzw : z ≠ w)
    (hzw_adj : ¬G.Adj z w) :
    (∃ C : (G.induce (↑(D.erase x |>.erase y) : Set V)).ConnectedComponent,
      (⟨z, (show z ∈ (↑(D.erase x |>.erase y) : Set V) from by
        simpa [hz.2.2.1, hz.2.2.2.1] using hz.1)⟩ :
        (↑(D.erase x |>.erase y) : Set V)) ∈ C.supp ∧
      (⟨w, (show w ∈ (↑(D.erase x |>.erase y) : Set V) from by
        simpa [hw.2.2.1, hw.2.2.2.1] using hw.1)⟩ :
        (↑(D.erase x |>.erase y) : Set V)) ∈ C.supp) ∨
    ∃ K : Finset V,
      z ∈ K ∧ K ⊆ D ∧ K ⊂ D ∧
      w ∉ K ∧ x ∉ K ∧ y ∉ K ∧
      (G.induce (↑K : Set V)).Connected ∧
      (∀ u, u ∈ K → ∀ v, v ∉ K → G.Adj u v → v = x) := by
  classical
  let S : Set V := (↑(D.erase x |>.erase y) : Set V)
  have hzS : z ∈ S := by
    simp [S, hz.1, hz.2.2.1, hz.2.2.2.1]
  have hwS : w ∈ S := by
    simp [S, hw.1, hw.2.2.1, hw.2.2.2.1]
  let H := G.induce S
  let Cz : H.ConnectedComponent := H.connectedComponentMk ⟨z, hzS⟩
  have hzC : (⟨z, hzS⟩ : S) ∈ Cz.supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  by_cases hwC : (⟨w, hwS⟩ : S) ∈ Cz.supp
  · exact Or.inl ⟨Cz, hzC, hwC⟩
  · right
    let K : Finset V := separatedThirdNeighborComponentCarrier G D x y Cz
    have hzK : z ∈ K := by
      apply (separatedThirdNeighborComponentCarrier_mem_iff G D x y Cz z).2
      exact ⟨hzS, hzC⟩
    have hKsub : K ⊆ D := by
      intro v hv
      obtain ⟨hvS, _⟩ :=
        (separatedThirdNeighborComponentCarrier_mem_iff G D x y Cz v).1 hv
      have hvD' : v ∈ (D.erase x).erase y := by simpa [S] using hvS
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp hvD').2).2
    have hKnotxy : ∀ v, v ∈ K → v ≠ x ∧ v ≠ y := by
      intro v hv
      obtain ⟨hvS, _⟩ :=
        (separatedThirdNeighborComponentCarrier_mem_iff G D x y Cz v).1 hv
      have hvD' : v ∈ (D.erase x).erase y := by simpa [S] using hvS
      exact ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp hvD').2).1,
        (Finset.mem_erase.mp hvD').1⟩
    have hwK : w ∉ K := by
      intro hwK
      obtain ⟨hwS', hwC'⟩ :=
        (separatedThirdNeighborComponentCarrier_mem_iff G D x y Cz w).1 hwK
      have hwC'' : (⟨w, hwS⟩ : S) ∈ Cz.supp := by
        simpa only [Subsingleton.elim hwS' hwS] using hwC'
      exact hwC hwC''
    have hxK : x ∉ K := by
      intro hxK
      exact (hKnotxy x hxK).1 rfl
    have hyK : y ∉ K := by
      intro hyK
      exact (hKnotxy y hyK).2 rfl
    have hKconn : (G.induce (↑K : Set V)).Connected := by
      refine { preconnected := ?_, nonempty := ⟨⟨z, hzK⟩⟩ }
      rintro ⟨u, huK⟩ ⟨v, hvK⟩
      obtain ⟨huS, huC⟩ :=
        (separatedThirdNeighborComponentCarrier_mem_iff G D x y Cz u).1 huK
      obtain ⟨hvS, hvC⟩ :=
        (separatedThirdNeighborComponentCarrier_mem_iff G D x y Cz v).1 hvK
      have huS' : u ∈ S := by
        simpa [S, and_assoc, and_left_comm, and_comm] using huS
      have hvS' : v ∈ S := by
        simpa [S, and_assoc, and_left_comm, and_comm] using hvS
      have huC' : (⟨u, huS'⟩ : S) ∈ Cz.supp := by
        simpa only [Subsingleton.elim huS huS'] using huC
      have hvC' : (⟨v, hvS'⟩ : S) ∈ Cz.supp := by
        simpa only [Subsingleton.elim hvS hvS'] using hvC
      obtain ⟨q, hq⟩ := Cz.connected_toSimpleGraph.exists_isPath
        (⟨⟨u, huS'⟩, huC'⟩ : Cz) (⟨⟨v, hvS'⟩, hvC'⟩ : Cz)
      let e : Cz.toSimpleGraph →g G :=
        { toFun := fun a => a.1.1
          map_rel' := fun h => h }
      let p : G.Walk u v := q.map e
      have hpK : ∀ a, a ∈ p.support → a ∈ K := by
        intro a ha
        rw [SimpleGraph.Walk.support_map] at ha
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
        exact (separatedThirdNeighborComponentCarrier_mem_iff G D x y Cz b.1.1).2
          ⟨b.1.2, b.2⟩
      exact (p.induce (↑K : Set V) hpK).reachable
    have hy_unique : ∀ u, u ∈ D → u ≠ x → G.Adj y u → u = w := by
      intro u huD hux hyu
      have hyaccount := two_cubic_ports_boundary_accounting D r x y hr hports
        hboundary hexact hcubic
      have hF : (D.filter (G.Adj y)).card = 2 := by
        simpa [internalDegree] using hyaccount.2.1
      have hxF : x ∈ D.filter (G.Adj y) :=
        Finset.mem_filter.mpr ⟨hports.1, hxy.symm⟩
      have hwF : w ∈ D.filter (G.Adj y) :=
        Finset.mem_filter.mpr ⟨hw.1, hw.2.2.2.2⟩
      have huF : u ∈ D.filter (G.Adj y) := Finset.mem_filter.mpr ⟨huD, hyu⟩
      have hcard : ({x, w, u} : Finset V).card ≤ (D.filter (G.Adj y)).card :=
        Finset.card_le_card (by
          intro v hv
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl | rfl
          · exact hxF
          · exact hwF
          · exact huF)
      by_cases huw : u = w
      · exact huw
      have huxw : x ≠ w := hw.2.2.1.symm
      have hxu : x ≠ u := by
        intro h
        exact hux h.symm
      have hwu : w ≠ u := by
        intro h
        exact huw h.symm
      have : ({x, w, u} : Finset V).card = 3 := by
        simp [huxw, hxu, hwu]
      omega
    have hboundaryK :
        ∀ u, u ∈ K → ∀ v, v ∉ K → G.Adj u v → v = x := by
      intro u huK v hvK huv
      have huD := hKsub huK
      by_cases hvD : v ∈ D
      · by_cases hvx : v = x
        · exact hvx
        · by_cases hvy : v = y
          · subst v
            have huw : u = w := hy_unique u huD (hKnotxy u huK).1 huv.symm
            exact (hwK (huw ▸ huK)).elim
          · have hvS : v ∈ S := by
              simp [S, hvD, hvx, hvy]
            have huS : u ∈ S := by
              obtain ⟨huS, _⟩ :=
                (separatedThirdNeighborComponentCarrier_mem_iff G D x y Cz u).1 huK
              simpa [S, and_assoc, and_left_comm, and_comm] using huS
            have huC : (⟨u, huS⟩ : S) ∈ Cz.supp := by
              obtain ⟨huS', huC'⟩ :=
                (separatedThirdNeighborComponentCarrier_mem_iff G D x y Cz u).1 huK
              have huS'' : u ∈ S := by
                simpa [S, and_assoc, and_left_comm, and_comm] using huS'
              simpa only [Subsingleton.elim huS'' huS] using huC'
            have hvC : (⟨v, hvS⟩ : S) ∈ Cz.supp :=
              Cz.mem_supp_of_adj_mem_supp huC huv
            have hvK' :=
              (separatedThirdNeighborComponentCarrier_mem_iff G D x y Cz v).2 ⟨hvS, hvC⟩
            exact (hvK hvK').elim
      · have hvr : v = r := hboundary u huD v hvD huv
        have hur : G.Adj u r := hvr ▸ huv
        rcases (hexact u huD).mp hur with hux' | huy'
        · exact (hKnotxy u huK).1 hux' |>.elim
        · exact (hKnotxy u huK).2 huy' |>.elim
    refine ⟨K, hzK, hKsub, ?_, hwK, hxK, hyK, hKconn, hboundaryK⟩
    refine ⟨hKsub, ?_⟩
    intro hDK
    exact hwK (hDK hw.1)

end Erdos64
