import Tengoku.Erdos64.Erdos64.CutSideDyadicEar
import Tengoku.Erdos64.Erdos64.PortPathExternalNeighbor
import Tengoku.Erdos64.Erdos64.GeneralBoundaryAvoidance

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Native off-path components have a nonempty carrier, boundary on the
port walk, and the strict half-order bound required by carrier forcing.-/
theorem cut_side_offPath_carrier_data
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (r : V)
    (C D : (G.induce {v : V | v ≠ r}).ConnectedComponent) (hCD : C ≠ D)
    {x y : V} (hxy : x ≠ y) (hrx : G.Adj r x) (hry : G.Adj r y)
    (p : G.Walk x y)
    (hinside : ∀ v, v ∈ p.support → v ∈ rootDeletedComponentCarrier G r C)
    (E : (G.induce {v : V | v ∈ rootDeletedComponentCarrier G r C ∧
      v ∉ p.support}).ConnectedComponent) :
    let K := offPathComponentCarrier G (rootDeletedComponentCarrier G r C) p E
    K.Nonempty ∧
      (∀ v, v ∈ K → v ∈ rootDeletedComponentCarrier G r C ∧ v ∉ p.support) ∧
      (∀ v, v ∈ K → ∀ w, w ∉ K → G.Adj v w → w ∈ p.support) ∧
      2 * K.card + 1 < Fintype.card V := by
  classical
  let := Fintype.ofFinite ((G.induce {v : V | v ≠ r}).ConnectedComponent)
  let A := rootDeletedComponentCarrier G r C
  let K := offPathComponentCarrier G A p E
  have hKdata : ∀ v, v ∈ K → v ∈ A ∧ v ∉ p.support := by
    intro v hv
    obtain ⟨hv, _⟩ := (mem_offPathComponentCarrier_iff G A p E v).mp hv
    exact hv
  have hK : K.Nonempty := by
    obtain ⟨⟨v, hv⟩, hvE⟩ := E.nonempty_supp
    exact ⟨v, (mem_offPathComponentCarrier_iff G A p E v).mpr ⟨hv, hvE⟩⟩
  have hcard : (rootDeletedComponentAttachments G r C).card = 2 :=
    (M.rootDeleted_two_components_exact_balanced r C D hCD).2.2.1
  have hxA : x ∈ A := hinside x p.start_mem_support
  have hyA : y ∈ A := hinside y p.end_mem_support
  have hpair : ({x, y} : Finset V) = rootDeletedComponentAttachments G r C := by
    apply Finset.eq_of_subset_of_card_le
    · intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with hax | hay
      · subst a
        exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset r x).mpr hrx, hxA⟩
      · subst a
        exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset r y).mpr hry, hyA⟩
    · simp [hcard, hxy]
  have hports : ∀ v, v ∈ A → G.Adj v r → v ∈ p.support := by
    intro v hv hvr
    have hvB : v ∈ rootDeletedComponentAttachments G r C :=
      Finset.mem_filter.mpr ⟨(G.mem_neighborFinset r v).mpr hvr.symm, hv⟩
    rw [← hpair] at hvB
    rcases Finset.mem_insert.mp hvB with h | h
    · simpa only [h] using p.start_mem_support
    · have h : v = y := Finset.mem_singleton.mp h
      simpa only [h] using p.end_mem_support
  have hboundary : ∀ v, v ∈ K → ∀ w, w ∉ K → G.Adj v w → w ∈ p.support := by
    intro v hv w hw hvw
    by_contra hwp
    obtain ⟨hvA, hvp⟩ := hKdata v hv
    have hwA : w ∈ A := by
      rcases (rootDeletedComponent_boundary r M.isConnected C).1 v hvA w hvw with
        hwA | hwr
      · exact hwA
      · have hvr : G.Adj v r := hwr ▸ hvw
        exact (hvp (hports v hvA hvr)).elim
    obtain ⟨hv', hvE⟩ := (mem_offPathComponentCarrier_iff G A p E v).mp hv
    have hEadj : (G.induce {z : V | z ∈ A ∧ z ∉ p.support}).Adj
        ⟨v, hv'⟩ ⟨w, ⟨hwA, hwp⟩⟩ := hvw
    exact hw ((mem_offPathComponentCarrier_iff G A p E w).mpr
      ⟨⟨hwA, hwp⟩, E.mem_supp_of_adj_mem_supp hvE hEadj⟩)
  have hKlt : K.card < A.card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨fun v hv => (hKdata v hv).1, ?_⟩
    intro hKA
    have hxK : x ∈ K := hKA.symm ▸ hxA
    exact (hKdata x hxK).2 p.start_mem_support
  have horder := M.rootDeleted_two_components_order r C D hCD
  have hsize : 2 * K.card + 1 < Fintype.card V := by
    change 2 * A.card + 1 = Fintype.card V at horder
    omega
  exact ⟨hK, hKdata, hboundary, hsize⟩

/-- A component outside a simple port path with at least four boundary
vertices supplies a fresh dyadic ear avoiding any specified cubic vertex of
the path. Only that selected vertex must be cubic. Its unique incidence into
the exterior component is derived from the path and root incidences.-/
theorem MinimalCounterexample.rootDeleted_cut_side_dyadic_ear_avoiding_cubic_path_vertex
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (r : V)
    (C D : (G.induce {v : V | v ≠ r}).ConnectedComponent) (hCD : C ≠ D)
    {x y : V} (hxy : x ≠ y) (hrx : G.Adj r x) (hry : G.Adj r y)
    (p : G.Walk x y) (hp : p.IsPath)
    (hinside : ∀ v, v ∈ p.support → v ∈ rootDeletedComponentCarrier G r C)
    (E : (G.induce {v : V | v ∈ rootDeletedComponentCarrier G r C ∧
      v ∉ p.support}).ConnectedComponent)
    (hB : 4 ≤ (carrierBoundaryVertices G
      (offPathComponentCarrier G (rootDeletedComponentCarrier G r C) p E)).card)
    (s : V) (hs : s ∈ p.support) (hsdeg : G.degree s = 3) :
    ∃ k : ℕ, ∃ a b : V, ∃ ear : G.Walk a b,
      1 ≤ k ∧ a ∈ p.support ∧ b ∈ p.support ∧ a ≠ b ∧
      ear.IsPath ∧ ear.length = 2 ^ k ∧
      (∀ v, v ∈ ear.support → v = a ∨ v = b ∨
        v ∈ offPathComponentCarrier G (rootDeletedComponentCarrier G r C) p E) ∧
      (∀ v, v ∈ ear.support → v ∈ p.support → v = a ∨ v = b) ∧
      s ∉ ear.support ∧
      (∀ v, v ∈ ear.support → v ∈ rootDeletedComponentCarrier G r C) := by
  classical
  let K := offPathComponentCarrier G (rootDeletedComponentCarrier G r C) p E
  obtain ⟨hK, hKdata, hboundary, hsize⟩ :=
    cut_side_offPath_carrier_data M r C D hCD hxy hrx hry p hinside E
  obtain ⟨t, hunique⟩ : ∃ t : {v : V // v ∈ K},
      ∀ v, v ∈ K → G.Adj v s → v = t.1 := by
    by_cases hattach : ∃ t, t ∈ K ∧ G.Adj t s
    · obtain ⟨t, ht, hts⟩ := hattach
      refine ⟨⟨t, ht⟩, ?_⟩
      intro v hv hvs
      exact cut_side_port_path_external_neighbors_eq r C hxy hrx hry p hp hinside
        K hKdata s hs hsdeg v hv t ht hvs.symm hts.symm
    · obtain ⟨t, ht⟩ := hK
      refine ⟨⟨t, ht⟩, ?_⟩
      intro v hv hvs
      exact (hattach ⟨v, hv, hvs⟩).elim
  obtain ⟨k, a, b, ear, hk, ha, hb, hab, hear, hlen, hsupport, hfresh, hsavoid⟩ :=
    M.small_carrier_dyadic_ear_avoiding_unique_attachment K {v | v ∈ p.support}
      (fun v hv => (hKdata v hv).2) hboundary hB hsize t s hs hunique
  refine ⟨k, a, b, ear, hk, ha, hb, hab, hear, hlen, hsupport, hfresh, hsavoid, ?_⟩
  intro v hv
  rcases hsupport v hv with hva | hvb | hvK
  · subst v
    exact hinside a ha
  · subst v
    exact hinside b hb
  · exact (hKdata v hvK).1

end Erdos64
