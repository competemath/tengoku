import Tengoku.Erdos64.Erdos64.SmallCarrierDyadicEar
import Tengoku.Erdos64.Erdos64.MinimalCounterexampleUniqueCut

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- The ambient vertices of one component inside a carrier after deleting
the support of a walk.-/
noncomputable def offPathComponentCarrier
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Finset V) {x y : V} (p : G.Walk x y)
    (E : (G.induce {v : V | v ∈ A ∧ v ∉ p.support}).ConnectedComponent) : Finset V := by
  classical
  exact E.supp.toFinset.image Subtype.val

/--
@isnad1 id=iff.0h8v.s8.91e256bd80b8 from=translated src=- shape=c1cf23f5 vocab=23b14fa7
-/
@[simp] theorem mem_offPathComponentCarrier_iff
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Finset V) {x y : V} (p : G.Walk x y)
    (E : (G.induce {v : V | v ∈ A ∧ v ∉ p.support}).ConnectedComponent) (v : V) :
    v ∈ offPathComponentCarrier G A p E ↔
      ∃ hv : v ∈ A ∧ v ∉ p.support,
        (⟨v, hv⟩ : {w : V // w ∈ A ∧ w ∉ p.support}) ∈ E.supp := by
  classical
  simp [offPathComponentCarrier]

/-- Every component outside a port walk in a balanced cut side contains the
interior of a fresh ear of power-of-two length. Exponent one allows a
two-edge ear; the attachments and exponent are produced by minimality.
@isnad1 id=ex.6h9v.s8.c8fc3541d30d from=translated src=- shape=0cfa945d vocab=55cb49c2
-/
theorem MinimalCounterexample.rootDeleted_cut_side_component_dyadic_ear
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (r : V)
    (C D : (G.induce {v : V | v ≠ r}).ConnectedComponent) (hCD : C ≠ D)
    {x y : V} (hxy : x ≠ y) (hrx : G.Adj r x) (hry : G.Adj r y)
    (p : G.Walk x y)
    (hinside : ∀ v, v ∈ p.support → v ∈ rootDeletedComponentCarrier G r C)
    (E : (G.induce {v : V | v ∈ rootDeletedComponentCarrier G r C ∧
      v ∉ p.support}).ConnectedComponent) :
    ∃ k : ℕ, ∃ a b : V, ∃ ear : G.Walk a b,
      1 ≤ k ∧ a ∈ p.support ∧ b ∈ p.support ∧ a ≠ b ∧
      ear.IsPath ∧ ear.length = 2 ^ k ∧
      (∀ v, v ∈ ear.support → v = a ∨ v = b ∨
        v ∈ offPathComponentCarrier G (rootDeletedComponentCarrier G r C) p E) ∧
      (∀ v, v ∈ ear.support → v ∈ p.support → v = a ∨ v = b) ∧
      (∀ v, v ∈ ear.support → v ∈ rootDeletedComponentCarrier G r C) := by
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
  obtain ⟨k, a, b, ear, hk, ha, hb, hab, hear, hlen, hsupport, hfresh⟩ :=
    M.small_carrier_dyadic_ear K {v | v ∈ p.support} hK
      (fun v hv => (hKdata v hv).2) hboundary hsize
  refine ⟨k, a, b, ear, hk, ha, hb, hab, hear, hlen, hsupport, hfresh, ?_⟩
  intro v hv
  rcases hsupport v hv with hva | hvb | hvK
  · subst v
    exact hinside a ha
  · subst v
    exact hinside b hb
  · exact (hKdata v hvK).1

/-- A vertex of a balanced cut side outside a port walk guarantees a fresh
dyadic ear inside that side. No external-component or ear witness is assumed.
@isnad1 id=ex.8h9v.s8.9f8b3bade691 from=translated src=- shape=863d07e7 vocab=3a7b4b2d
-/
theorem MinimalCounterexample.rootDeleted_cut_side_dyadic_ear_of_external_vertex
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (r : V)
    (C D : (G.induce {v : V | v ≠ r}).ConnectedComponent) (hCD : C ≠ D)
    {x y : V} (hxy : x ≠ y) (hrx : G.Adj r x) (hry : G.Adj r y)
    (p : G.Walk x y)
    (hinside : ∀ v, v ∈ p.support → v ∈ rootDeletedComponentCarrier G r C)
    (w : V) (hw : w ∈ rootDeletedComponentCarrier G r C) (hwp : w ∉ p.support) :
    ∃ k : ℕ, ∃ a b : V, ∃ ear : G.Walk a b,
      1 ≤ k ∧ a ∈ p.support ∧ b ∈ p.support ∧ a ≠ b ∧
      ear.IsPath ∧ ear.length = 2 ^ k ∧
      (∀ v, v ∈ ear.support → v ∈ p.support → v = a ∨ v = b) ∧
      (∀ v, v ∈ ear.support → v ∈ rootDeletedComponentCarrier G r C) := by
  let E := (G.induce {v : V | v ∈ rootDeletedComponentCarrier G r C ∧
    v ∉ p.support}).connectedComponentMk ⟨w, ⟨hw, hwp⟩⟩
  obtain ⟨k, a, b, ear, hk, ha, hb, hab, hear, hlen, _, hfresh, hside⟩ :=
    M.rootDeleted_cut_side_component_dyadic_ear r C D hCD hxy hrx hry p hinside E
  exact ⟨k, a, b, ear, hk, ha, hb, hab, hear, hlen, hfresh, hside⟩

end Erdos64
