import Tengoku.Erdos64.Erdos64.TwoPortDefectBookkeeping

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- A finite cubic two-pole has an even number of carrier vertices.  The
boundary consists of one edge at each of two distinct ports, so the induced
edge count satisfies the exact cubic handshake equation.-/
theorem two_pole_cubic_even_order
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (D : Finset V) (r x y : V)
    (hr : r ∉ D)
    (hports : x ∈ D ∧ y ∈ D ∧ x ≠ y)
    (hboundary :
      ∀ v, v ∈ D → ∀ w, w ∉ D → G.Adj v w → w = r)
    (hexact :
      ∀ v, v ∈ D → (G.Adj v r ↔ v = x ∨ v = y))
    (hcubic : ∀ v, v ∈ D → G.degree v = 3) :
    2 * (G.induce (↑D : Set V)).edgeFinset.card + 2 = 3 * D.card ∧
      Even D.card := by
  classical
  obtain ⟨hxdeg, hydeg, hnonport, _⟩ :=
    two_cubic_ports_boundary_accounting D r x y hr hports hboundary
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
  have hcard_lower : 2 ≤ D.card := by
    have hsub : ({x, y} : Finset V) ⊆ D := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact hports.1
      · exact hports.2.1
    have hcard := Finset.card_le_card hsub
    simpa [hports.2.2] using hcard
  have hsum_eval :
      D.sum (fun v => internalDegree G D v) = 3 * D.card - 2 := by
    have hcardD : ((D.erase x).erase y).card = D.card - 2 := by
      calc
        ((D.erase x).erase y).card = (D.erase x).card - 1 :=
          Finset.card_erase_of_mem hy_erase
        _ = (D.card - 1) - 1 := by
          rw [Finset.card_erase_of_mem hports.1]
        _ = D.card - 2 := by simp [Nat.sub_sub]
    have hnon_sum' := hnon_sum
    rw [hcardD] at hnon_sum'
    rw [← Finset.add_sum_erase D (fun v => internalDegree G D v) hports.1]
    rw [← Finset.add_sum_erase (D.erase x)
      (fun v => internalDegree G D v) hy_erase]
    rw [hxdeg, hydeg, hnon_sum']
    omega
  have hEq :
      2 * (G.induce (↑D : Set V)).edgeFinset.card + 2 = 3 * D.card := by
    calc
      2 * (G.induce (↑D : Set V)).edgeFinset.card + 2 =
          D.sum (fun v => internalDegree G D v) + 2 := by rw [hsum]
      _ = (3 * D.card - 2) + 2 := by rw [hsum_eval]
      _ = 3 * D.card := by
        have hthree : 2 ≤ 3 * D.card := by omega
        exact Nat.sub_add_cancel hthree
  constructor
  · exact hEq
  · have hparity : 2 ∣ 3 * D.card := by
      use (G.induce (↑D : Set V)).edgeFinset.card + 1
      omega
    rw [even_iff_two_dvd]
    omega

end Erdos64
