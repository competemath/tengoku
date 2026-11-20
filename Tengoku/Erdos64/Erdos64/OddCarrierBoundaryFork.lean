import Tengoku.Erdos64.Erdos64.CutSideDyadicEarAvoidance
import Tengoku.Seed.Algebra.BigOperators.Ring.Nat
import Tengoku.Seed.Combinatorics.SimpleGraph.DegreeSum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- The number of incidences directed from a carrier to its complement is
odd when the carrier has odd order and all its ambient degrees are odd.
Each crossing edge contributes exactly once to this sum.
@isnad1 id=odd.2h3v.s7.8f38ffde98a8 from=translated src=- shape=6c331b95 vocab=9a497e8a
-/
theorem carrier_external_degree_sum_odd
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (K : Finset V) (hKodd : Odd K.card)
    (hodddegrees : ∀ v, v ∈ K → Odd (G.degree v)) :
    Odd (∑ v : (↑K : Set V),
      ((G.neighborFinset v.1).filter (fun w => w ∉ K)).card) := by
  classical
  let H := G.induce (↑K : Set V)
  have hdegree : ∀ v : (↑K : Set V),
      H.degree v + ((G.neighborFinset v.1).filter (fun w => w ∉ K)).card =
        G.degree v.1 := by
    intro v
    have hinside : (G.neighborFinset v.1).filter (fun w => w ∈ K) =
        K.filter (G.Adj v.1) := by
      ext w
      simp [and_comm]
    have hsplit := (G.neighborFinset v.1).card_filter_add_card_filter_not
      (fun w => w ∈ K)
    rw [hinside] at hsplit
    simpa only [H, degree_induce_coeFinset_eq_internalDegree, internalDegree,
      SimpleGraph.card_neighborFinset_eq_degree] using hsplit
  have hfilter : Finset.univ.filter (fun v : (↑K : Set V) =>
      Odd (G.degree v.1)) = Finset.univ := by
    ext v
    simp [hodddegrees v.1 v.2]
  have hsumodd : Odd (∑ v : (↑K : Set V), G.degree v.1) := by
    apply (Finset.odd_sum_iff_odd_card_odd _).mpr
    rw [hfilter, Finset.card_univ]
    simpa using hKodd
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) (by rfl)
    (fun v _ => hdegree v)
  rw [Finset.sum_add_distrib, H.sum_degrees_eq_twice_card_edges] at hsum
  obtain ⟨k, hk⟩ := hsumodd
  exact ⟨k - H.edgeFinset.card, by omega⟩

/-- In particular, an odd carrier of odd-degree vertices cannot have
exactly two crossing edges, including the case where they share an endpoint.
@isnad1 id=ne.2h3v.s7.857445d02700 from=translated src=- shape=376641f3 vocab=9a497e8a
-/
theorem odd_carrier_external_degree_sum_ne_two
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (K : Finset V) (hKodd : Odd K.card)
    (hodddegrees : ∀ v, v ∈ K → Odd (G.degree v)) :
    (∑ v : (↑K : Set V),
      ((G.neighborFinset v.1).filter (fun w => w ∉ K)).card) ≠ 2 := by
  obtain ⟨k, hk⟩ := carrier_external_degree_sum_odd K hKodd hodddegrees
  omega

/-- If each carrier vertex has at most one external neighbor, the crossing
edge count is the number of internal boundary vertices.
@isnad1 id=odd.3h3v.s7.b470f83f9dae from=translated src=- shape=cebab480 vocab=00940288
-/
theorem carrier_boundary_card_odd_of_single_external_neighbor
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (K : Finset V) (hKodd : Odd K.card)
    (hodddegrees : ∀ v, v ∈ K → Odd (G.degree v))
    (hsingle : ∀ v, v ∈ K → ∀ a, a ∉ K → ∀ b, b ∉ K →
      G.Adj v a → G.Adj v b → a = b) :
    Odd (carrierBoundaryVertices G K).card := by
  classical
  let H := G.induce (↑K : Set V)
  let B := carrierBoundaryVertices G K
  have hfilter : Finset.univ.filter (fun v : (↑K : Set V) =>
      Odd (G.degree v.1)) = Finset.univ := by
    ext v
    simp [hodddegrees v.1 v.2]
  have hsumodd : Odd (∑ v : (↑K : Set V), G.degree v.1) := by
    apply (Finset.odd_sum_iff_odd_card_odd _).mpr
    rw [hfilter, Finset.card_univ]
    simpa using hKodd
  have hsum : (∑ v : (↑K : Set V), (H.degree v +
      (if v ∈ B then 1 else 0))) = ∑ v : (↑K : Set V), G.degree v.1 := by
    apply Finset.sum_congr rfl
    intro v _
    exact carrier_degree_add_boundary_indicator K hsingle v
  have hsumB : (∑ v : (↑K : Set V), if v ∈ B then 1 else 0) = B.card := by
    exact (Finset.card_eq_sum_ite (Finset.subset_univ B)).symm
  rw [Finset.sum_add_distrib, hsumB, H.sum_degrees_eq_twice_card_edges] at hsum
  obtain ⟨k, hk⟩ := hsumodd
  change Odd B.card
  exact ⟨k - H.edgeFinset.card, by omega⟩

/-- An even number of internal boundary vertices forces two external
neighbors at one carrier vertex. This is a parity theorem and requires no
minimality, degree lower bound, connectivity, or size assumption.
@isnad1 id=ex.3h3v.s7.754824ff3fac from=translated src=- shape=db37ceba vocab=bd8e79dc
-/
theorem odd_carrier_even_boundary_fork
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (K : Finset V) (hKodd : Odd K.card)
    (hodddegrees : ∀ v, v ∈ K → Odd (G.degree v))
    (hB : Even (carrierBoundaryVertices G K).card) :
    ∃ v ∈ K, ∃ a, a ∉ K ∧ ∃ b, b ∉ K ∧
      a ≠ b ∧ G.Adj v a ∧ G.Adj v b := by
  by_contra hfork
  have hsingle : ∀ v, v ∈ K → ∀ a, a ∉ K → ∀ b, b ∉ K →
      G.Adj v a → G.Adj v b → a = b := by
    intro v hv a ha b hb hva hvb
    by_contra hab
    exact hfork ⟨v, hv, a, ha, b, hb, hab, hva, hvb⟩
  exact (Nat.not_odd_iff_even.mpr hB)
    (carrier_boundary_card_odd_of_single_external_neighbor K hKodd hodddegrees hsingle)

/-- A small odd carrier with at most two internal boundary vertices must
contain a fork. The potential one-boundary case is excluded by the existing
one-defect minimality argument when every carrier vertex has at most one
external neighbor.
@isnad1 id=ex.5h3v.s7.45bb78bcf7ee from=translated src=- shape=b248f469 vocab=520b5823
-/
theorem MinimalCounterexample.small_odd_carrier_low_boundary_fork
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (K : Finset V) (hKodd : Odd K.card)
    (hodddegrees : ∀ v, v ∈ K → Odd (G.degree v))
    (hsize : 2 * K.card + 1 < Fintype.card V)
    (hB : (carrierBoundaryVertices G K).card ≤ 2) :
    ∃ v ∈ K, ∃ a, a ∉ K ∧ ∃ b, b ∉ K ∧
      a ≠ b ∧ G.Adj v a ∧ G.Adj v b := by
  by_contra hfork
  have hsingle : ∀ v, v ∈ K → ∀ a, a ∉ K → ∀ b, b ∉ K →
      G.Adj v a → G.Adj v b → a = b := by
    intro v hv a ha b hb hva hvb
    by_contra hab
    exact hfork ⟨v, hv, a, ha, b, hb, hab, hva, hvb⟩
  have hBtwo := M.small_carrier_boundary_card_ge_two K
    (Finset.card_pos.mp hKodd.pos) hsingle hsize
  obtain ⟨k, hk⟩ :=
    carrier_boundary_card_odd_of_single_external_neighbor K hKodd hodddegrees hsingle
  omega

/-- For an odd off-path component with at most two boundary vertices, the
fork-or-ear-spectrum alternative reduces to a two-edge ear. Neither cubic
path degrees nor simplicity or parity of the port walk is needed here.
@isnad1 id=other.9h9v.s9.d0f7efae1a44 from=translated src=- shape=87035388 vocab=9bb3dcc1
-/
theorem MinimalCounterexample.rootDeleted_odd_low_boundary_component_two_edge_ear
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (r : V)
    (C D : (G.induce {v : V | v ≠ r}).ConnectedComponent) (hCD : C ≠ D)
    {x y : V} (hxy : x ≠ y) (hrx : G.Adj r x) (hry : G.Adj r y)
    (p : G.Walk x y)
    (hinside : ∀ z, z ∈ p.support → z ∈ rootDeletedComponentCarrier G r C)
    (E : (G.induce {z : V | z ∈ rootDeletedComponentCarrier G r C ∧
      z ∉ p.support}).ConnectedComponent)
    (hKodd : Odd (offPathComponentCarrier G
      (rootDeletedComponentCarrier G r C) p E).card)
    (hodddegrees : ∀ v, v ∈ offPathComponentCarrier G
      (rootDeletedComponentCarrier G r C) p E → Odd (G.degree v))
    (hB : (carrierBoundaryVertices G
      (offPathComponentCarrier G (rootDeletedComponentCarrier G r C) p E)).card ≤ 2) :
    let K := offPathComponentCarrier G (rootDeletedComponentCarrier G r C) p E
    ∃ u a b : V, ∃ ear : G.Walk a b,
      u ∈ K ∧ a ∈ p.support ∧ b ∈ p.support ∧ a ≠ b ∧
      G.Adj u a ∧ G.Adj u b ∧ ear.IsPath ∧ ear.length = 2 ∧
      (∀ z, z ∈ ear.support → z = a ∨ z = b ∨ z ∈ K) ∧
      (∀ z, z ∈ ear.support → z ∈ p.support → z = a ∨ z = b) := by
  classical
  let K := offPathComponentCarrier G (rootDeletedComponentCarrier G r C) p E
  obtain ⟨_, hKdata, hboundary, hsize⟩ :=
    cut_side_offPath_carrier_data M r C D hCD hxy hrx hry p hinside E
  obtain ⟨u, hu, a, ha, b, hb, hab, hua, hub⟩ :=
    M.small_odd_carrier_low_boundary_fork K hKodd hodddegrees hsize hB
  let ear : G.Walk a b := .cons hua.symm (.cons hub .nil)
  have hear : ear.IsPath := by
    apply SimpleGraph.Walk.IsPath.cons (SimpleGraph.Walk.IsPath.of_adj hub)
    simp [hua.ne.symm, hab]
  have hsupport : ∀ z, z ∈ ear.support → z = a ∨ z = b ∨ z ∈ K := by
    intro z hz
    simp only [ear, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (h ▸ hu))
    · exact Or.inr (Or.inl h)
  refine ⟨u, a, b, ear, hu, hboundary u hu a ha hua,
    hboundary u hu b hb hub, hab, hua, hub, hear, rfl, hsupport, ?_⟩
  intro z hz hzp
  rcases hsupport z hz with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact ((hKdata z h).2 hzp).elim

end Erdos64
