import Tengoku.Erdos64.Erdos64.TwoPortDefectBookkeeping

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- A balanced two-port carrier forces an odd ambient order when its
    complement away from the root has the same size.  The complementary
    carrier is constructed internally, so the balance hypothesis does not
    duplicate the partition data required by the underlying bookkeeping
    theorem.-/
theorem balanced_two_cubic_poles_force_odd_ambient_order_of_complement_balanced
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (D : Finset V) (r x y : V)
    (hrD : r ∉ D) (hports : x ∈ D ∧ y ∈ D ∧ x ≠ y)
    (hboundary :
      ∀ v, v ∈ D → ∀ w, w ∉ D → G.Adj v w → w = r)
    (hexact :
      ∀ v, v ∈ D → (G.Adj v r ↔ v = x ∨ v = y))
    (hcubic : ∀ v, v ∈ D → G.degree v = 3)
    (hbalanced : D.card = (Finset.univ \ (D ∪ ({r} : Finset V))).card) :
    Even D.card ∧ Fintype.card V = 2 * D.card + 1 := by
  classical
  let E : Finset V := Finset.univ \ (D ∪ ({r} : Finset V))
  have hDE : Disjoint D E := by
    apply Finset.disjoint_left.2
    intro v hvD hvE
    exact (Finset.mem_sdiff.mp hvE).2
      (Finset.mem_union.mpr (Or.inl hvD))
  have hrE : r ∉ E := by
    intro hrE
    exact (Finset.mem_sdiff.mp hrE).2
      (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))
  have hpartition : (D ∪ E) ∪ ({r} : Finset V) = Finset.univ := by
    ext v
    by_cases hvr : v = r
    · simp [hvr]
    · by_cases hvD : v ∈ D
      · simp [hvr, hvD]
      · simp [E, hvr, hvD]
  have hequal : D.card = E.card := by
    simpa [E] using hbalanced
  obtain ⟨hxdeg, hydeg, hnonport, _⟩ :=
    two_cubic_ports_boundary_accounting D r x y hrD hports hboundary
      hexact ⟨hcubic x hports.1, hcubic y hports.2.1⟩
  have hsum :
      D.sum (fun v => internalDegree G D v) =
        2 * (G.induce (↑D : Set V)).edgeFinset.card := by
    let H : SimpleGraph (↑D : Set V) := G.induce (↑D : Set V)
    have hhand := H.sum_degrees_eq_twice_card_edges
    have hsum_bij :
        D.sum (fun v => internalDegree G D v) =
          (Finset.univ : Finset (↑D : Set V)).sum (fun v => H.degree v) := by
      refine Finset.sum_bij (fun a ha => ⟨a, ?_⟩) ?_ ?_ ?_ ?_
      · exact ha
      · simp
      · intro a₁ ha₁ a₂ ha₂ h
        exact congrArg Subtype.val h
      · intro b hb
        refine ⟨b.1, b.2, ?_⟩
        exact Subtype.ext rfl
      · intro a ha
        simpa [H] using
          (degree_induce_coeFinset_eq_internalDegree G ⟨a, ha⟩).symm
    calc
      D.sum (fun v => internalDegree G D v) =
          (Finset.univ : Finset (↑D : Set V)).sum (fun v => H.degree v) :=
        hsum_bij
      _ = 2 * H.edgeFinset.card := hhand
  have hy_erase : y ∈ D.erase x :=
    Finset.mem_erase.mpr ⟨hports.2.2.symm, hports.2.1⟩
  have hcard_lower : 2 ≤ D.card := by
    have hsubset : ({x, y} : Finset V) ⊆ D := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact hports.1
      · exact hports.2.1
    have hcard := Finset.card_le_card hsubset
    simpa [hports.2.2] using hcard
  have hnon_sum :
      ((D.erase x).erase y).sum (fun v => internalDegree G D v) =
        3 * ((D.erase x).erase y).card := by
    calc
      ((D.erase x).erase y).sum (fun v => internalDegree G D v) =
          ((D.erase x).erase y).sum (fun _ => 3) := by
            apply Finset.sum_congr rfl
            intro v hv
            have hvy : v ≠ y := (Finset.mem_erase.mp hv).1
            have hvx : v ≠ x :=
              (Finset.mem_erase.mp (Finset.mem_erase.mp hv).2).1
            have hvD : v ∈ D :=
              (Finset.mem_erase.mp (Finset.mem_erase.mp hv).2).2
            exact (hnonport v hvD hvx hvy).trans (hcubic v hvD)
      _ = 3 * ((D.erase x).erase y).card := by simp [Nat.mul_comm]
  have hsum_eval :
      D.sum (fun v => internalDegree G D v) = 3 * D.card - 2 := by
    rw [← Finset.add_sum_erase D (fun v => internalDegree G D v) hports.1]
    rw [← Finset.add_sum_erase (D.erase x)
      (fun v => internalDegree G D v) hy_erase]
    rw [hxdeg, hydeg, hnon_sum]
    have hcardD : ((D.erase x).erase y).card = D.card - 2 := by
      calc
        ((D.erase x).erase y).card = (D.erase x).card - 1 :=
          Finset.card_erase_of_mem hy_erase
        _ = (D.card - 1) - 1 := by
          rw [Finset.card_erase_of_mem hports.1]
        _ = D.card - 2 := by simp [Nat.sub_sub]
    rw [hcardD] at hnon_sum ⊢
    have hcardDsub : D.card - 2 + 2 = D.card := Nat.sub_add_cancel hcard_lower
    have hthree : 2 ≤ 3 * D.card := by omega
    symm
    apply (Nat.sub_eq_iff_eq_add hthree).2
    clear hnon_sum hcardD
    rw [← hcardDsub]
    simp [Nat.mul_add]
    omega
  have hDeven : Even D.card := by
    have hthree : 2 ≤ 3 * D.card := by omega
    have hparity : 2 ∣ 3 * D.card := by
      use (G.induce (↑D : Set V)).edgeFinset.card + 1
      have hEq :
          2 * (G.induce (↑D : Set V)).edgeFinset.card + 2 = 3 * D.card := by
        calc
          2 * (G.induce (↑D : Set V)).edgeFinset.card + 2 =
              D.sum (fun v => internalDegree G D v) + 2 := by rw [hsum]
          _ = (3 * D.card - 2) + 2 := by rw [hsum_eval]
          _ = 3 * D.card := Nat.sub_add_cancel hthree
      calc
        3 * D.card =
            2 * (G.induce (↑D : Set V)).edgeFinset.card + 2 := hEq.symm
        _ = 2 * ((G.induce (↑D : Set V)).edgeFinset.card + 1) := by omega
    rw [even_iff_two_dvd]
    omega
  have hroot_disjoint : Disjoint (D ∪ E) ({r} : Finset V) := by
    apply Finset.disjoint_left.2
    intro v hvDE hvr
    rcases Finset.mem_union.mp hvDE with hvD | hvE
    · exact hrD (Finset.mem_singleton.mp hvr ▸ hvD)
    · exact hrE (Finset.mem_singleton.mp hvr ▸ hvE)
  have hcard : D.card + E.card + 1 = Fintype.card V := by
    calc
      D.card + E.card + 1 = ((D ∪ E) ∪ ({r} : Finset V)).card := by
        rw [Finset.card_union_of_disjoint hroot_disjoint,
          Finset.card_union_of_disjoint hDE,
          Finset.card_singleton]
      _ = Finset.univ.card := congrArg Finset.card hpartition
      _ = Fintype.card V := Finset.card_univ
  exact ⟨hDeven, by omega⟩

/-- Equal-sized exact cubic two-port sides have equal induced edge counts.
The equality is a consequence of the two-pole handshake identity on each
side, not an additional cut hypothesis.-/
theorem equal_induced_edge_count_of_equal_two_pole_card
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (D E : Finset V)
    (r xD yD xE yE : V)
    (hrD : r ∉ D)
    (hportsD : xD ∈ D ∧ yD ∈ D ∧ xD ≠ yD)
    (hboundaryD :
      ∀ v, v ∈ D → ∀ w, w ∉ D → G.Adj v w → w = r)
    (hexactD :
      ∀ v, v ∈ D → (G.Adj v r ↔ v = xD ∨ v = yD))
    (hcubicD : ∀ v, v ∈ D → G.degree v = 3)
    (hrE : r ∉ E)
    (hportsE : xE ∈ E ∧ yE ∈ E ∧ xE ≠ yE)
    (hboundaryE :
      ∀ v, v ∈ E → ∀ w, w ∉ E → G.Adj v w → w = r)
    (hexactE :
      ∀ v, v ∈ E → (G.Adj v r ↔ v = xE ∨ v = yE))
    (hcubicE : ∀ v, v ∈ E → G.degree v = 3)
    (hcard : D.card = E.card) :
    (G.induce (↑D : Set V)).edgeFinset.card =
      (G.induce (↑E : Set V)).edgeFinset.card := by
  have hhandshake :
      ∀ (S : Finset V) (x y : V),
        r ∉ S →
        (x ∈ S ∧ y ∈ S ∧ x ≠ y) →
        (∀ v, v ∈ S → ∀ w, w ∉ S → G.Adj v w → w = r) →
        (∀ v, v ∈ S → (G.Adj v r ↔ v = x ∨ v = y)) →
        (∀ v, v ∈ S → G.degree v = 3) →
        2 * (G.induce (↑S : Set V)).edgeFinset.card + 2 =
          3 * S.card := by
    intro S x y hrS hportsS hboundaryS hexactS hcubicS
    obtain ⟨hxdeg, hydeg, hnonport, _⟩ :=
      two_cubic_ports_boundary_accounting S r x y hrS hportsS
        hboundaryS hexactS
        ⟨hcubicS x hportsS.1, hcubicS y hportsS.2.1⟩
    have hsum :
        S.sum (fun v => internalDegree G S v) =
          2 * (G.induce (↑S : Set V)).edgeFinset.card := by
      let H : SimpleGraph (↑S : Set V) := G.induce (↑S : Set V)
      have hhand := H.sum_degrees_eq_twice_card_edges
      have hsum_bij :
          S.sum (fun v => internalDegree G S v) =
            (Finset.univ : Finset (↑S : Set V)).sum
              (fun v => H.degree v) := by
        refine Finset.sum_bij (fun a ha => ⟨a, ?_⟩) ?_ ?_ ?_ ?_
        · exact ha
        · simp
        · intro a₁ ha₁ a₂ ha₂ h
          exact congrArg Subtype.val h
        · intro b hb
          refine ⟨b.1, b.2, ?_⟩
          exact Subtype.ext rfl
        · intro a ha
          simpa [H] using
            (degree_induce_coeFinset_eq_internalDegree G ⟨a, ha⟩).symm
      calc
        S.sum (fun v => internalDegree G S v) =
            (Finset.univ : Finset (↑S : Set V)).sum
              (fun v => H.degree v) := hsum_bij
        _ = 2 * H.edgeFinset.card := hhand
    have hy_erase : y ∈ S.erase x :=
      Finset.mem_erase.mpr ⟨hportsS.2.2.symm, hportsS.2.1⟩
    have hcard_lower : 2 ≤ S.card := by
      have hsubset : ({x, y} : Finset V) ⊆ S := by
        intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact hportsS.1
        · exact hportsS.2.1
      have hcard := Finset.card_le_card hsubset
      simpa [hportsS.2.2] using hcard
    have hnon_sum :
        ((S.erase x).erase y).sum (fun v => internalDegree G S v) =
          3 * ((S.erase x).erase y).card := by
      calc
        ((S.erase x).erase y).sum (fun v => internalDegree G S v) =
            ((S.erase x).erase y).sum (fun _ => 3) := by
              apply Finset.sum_congr rfl
              intro v hv
              have hvy : v ≠ y := (Finset.mem_erase.mp hv).1
              have hvx : v ≠ x :=
                (Finset.mem_erase.mp (Finset.mem_erase.mp hv).2).1
              have hvS : v ∈ S :=
                (Finset.mem_erase.mp (Finset.mem_erase.mp hv).2).2
              exact (hnonport v hvS hvx hvy).trans (hcubicS v hvS)
        _ = 3 * ((S.erase x).erase y).card := by
          simp [Nat.mul_comm]
    have hsum_eval :
        S.sum (fun v => internalDegree G S v) = 3 * S.card - 2 := by
      rw [← Finset.add_sum_erase S (fun v => internalDegree G S v)
        hportsS.1]
      rw [← Finset.add_sum_erase (S.erase x)
        (fun v => internalDegree G S v) hy_erase]
      rw [hxdeg, hydeg, hnon_sum]
      have hcardS : ((S.erase x).erase y).card = S.card - 2 := by
        calc
          ((S.erase x).erase y).card = (S.erase x).card - 1 :=
            Finset.card_erase_of_mem hy_erase
          _ = (S.card - 1) - 1 := by
            rw [Finset.card_erase_of_mem hportsS.1]
          _ = S.card - 2 := by simp [Nat.sub_sub]
      rw [hcardS] at hnon_sum ⊢
      have hcardSsub : S.card - 2 + 2 = S.card :=
        Nat.sub_add_cancel hcard_lower
      have hthree : 2 ≤ 3 * S.card := by omega
      symm
      apply (Nat.sub_eq_iff_eq_add hthree).2
      clear hnon_sum hcardS
      rw [← hcardSsub]
      simp [Nat.mul_add]
      omega
    have hthree : 2 ≤ 3 * S.card := by omega
    calc
      2 * (G.induce (↑S : Set V)).edgeFinset.card + 2 =
          S.sum (fun v => internalDegree G S v) + 2 := by rw [hsum]
      _ = (3 * S.card - 2) + 2 := by rw [hsum_eval]
      _ = 3 * S.card := Nat.sub_add_cancel hthree
  have hD := hhandshake D xD yD hrD hportsD hboundaryD hexactD hcubicD
  have hE := hhandshake E xE yE hrE hportsE hboundaryE hexactE hcubicE
  omega

end Erdos64
