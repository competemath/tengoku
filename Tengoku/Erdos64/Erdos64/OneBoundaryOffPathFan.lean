import Tengoku.Erdos64.Erdos64.CutSideDyadicEarAvoidance
import Tengoku.Erdos64.Erdos64.ResidualPathRootSplit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- If deleting `t` leaves a connected graph, a proper carrier whose only
possible boundary vertex is `t` consists of `t` alone.
@isnad1 id=eq.4h5v.s6.5310487b0c26 from=translated src=- shape=59bf79d5 vocab=ecb479bf
-/
theorem carrier_eq_singleton_of_connected_vertex_deletion
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    (K : Finset V) (t : V) (ht : t ∈ K)
    (z : V) (hz : z ∉ K)
    (hconn : (G.induce {v : V | v ≠ t}).Connected)
    (hboundary : ∀ v, v ∈ K → ∀ w, w ∉ K → G.Adj v w → v = t) :
    K = {t} := by
  classical
  have hall : ∀ v, v ∈ K → v = t := by
    intro v hv
    by_contra hvt
    have hzt : z ≠ t := fun h => hz (h ▸ ht)
    obtain ⟨q, hq⟩ := hconn.exists_isPath ⟨v, hvt⟩ ⟨z, hzt⟩
    let e : G.induce {v : V | v ≠ t} ↪g G := SimpleGraph.Embedding.induce _
    let p : G.Walk v z := q.map e.toHom
    have hp : p.IsPath := hq.map e.injective
    have hav : t ∉ p.support := by
      intro h
      change t ∈ (q.map e.toHom).support at h
      rw [SimpleGraph.Walk.support_map] at h
      obtain ⟨w, _, hw⟩ := List.mem_map.mp h
      exact w.2 hw
    have hstart : v ∈ K.erase t := Finset.mem_erase.mpr ⟨hvt, hv⟩
    have hexit : ∀ a, a ∈ K.erase t → ∀ b, b ∉ K.erase t → G.Adj a b → b = t := by
      intro a ha b hb hab
      by_cases hbK : b ∈ K
      · by_contra hbt
        exact hb (Finset.mem_erase.mpr ⟨hbt, hbK⟩)
      · exact ((Finset.mem_erase.mp ha).1
          (hboundary a (Finset.mem_erase.mp ha).2 b hbK hab)).elim
    have hzinside := SimpleGraph.Walk.IsPath.support_subset_of_boundary_avoiding_root
      hp hstart hav hexit z p.end_mem_support
    exact hz (Finset.mem_erase.mp hzinside).2
  ext v
  simp only [Finset.mem_singleton]
  exact ⟨hall v, fun h => h ▸ ht⟩

/-- Away from the unique cut root, a nonempty carrier with at most one
boundary vertex is a singleton. No connectedness or size bound on the
carrier is assumed.
@isnad1 id=ex.5h4v.s7.f35624118024 from=translated src=- shape=c5da864c vocab=aedf84c3
-/
theorem MinimalCounterexample.carrier_singleton_of_boundary_card_le_one
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (r : V)
    (hcut : ∃ C D : (G.induce {v : V | v ≠ r}).ConnectedComponent, C ≠ D)
    (K : Finset V) (hK : K.Nonempty) (hrK : r ∉ K)
    (hB : (carrierBoundaryVertices G K).card ≤ 1) :
    ∃ t : V, K = {t} := by
  classical
  let B := carrierBoundaryVertices G K
  obtain ⟨t, ht⟩ : ∃ t : {v : V // v ∈ K}, ∀ v, v ∈ B → v = t := by
    by_cases hne : B.Nonempty
    · obtain ⟨t, ht⟩ := hne
      exact ⟨t, fun v hv => (Finset.card_le_one.mp hB) v hv t ht⟩
    · obtain ⟨t, ht⟩ := hK
      exact ⟨⟨t, ht⟩, fun v hv => (hne ⟨v, hv⟩).elim⟩
  have htr : t.1 ≠ r := fun h => hrK (h ▸ t.2)
  refine ⟨t.1, carrier_eq_singleton_of_connected_vertex_deletion K t.1 t.2 r hrK
    (M.rootDeleted_connected_away_from_cut r t.1 hcut htr) ?_⟩
  intro v hv w hw hvw
  have hvB : (⟨v, hv⟩ : {v : V // v ∈ K}) ∈ B :=
    (mem_carrierBoundaryVertices G K ⟨v, hv⟩).mpr ⟨w, hw, hvw⟩
  exact congrArg Subtype.val (ht ⟨v, hv⟩ hvB)

/-- A component outside a native port walk with at most one carrier boundary
vertex is a single vertex with three distinct neighbors on the walk. Thus
the one-boundary case is an actual three-attachment, two-edge-ear fan.
@isnad1 id=ex.7h9v.s8.3fba92cfa24d from=translated src=- shape=648a04bd vocab=8820bd82
-/
theorem MinimalCounterexample.rootDeleted_one_boundary_component_three_attachment_fan
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (r : V)
    (C D : (G.induce {v : V | v ≠ r}).ConnectedComponent) (hCD : C ≠ D)
    {x y : V} (hxy : x ≠ y) (hrx : G.Adj r x) (hry : G.Adj r y)
    (p : G.Walk x y)
    (hinside : ∀ v, v ∈ p.support → v ∈ rootDeletedComponentCarrier G r C)
    (E : (G.induce {v : V | v ∈ rootDeletedComponentCarrier G r C ∧
      v ∉ p.support}).ConnectedComponent)
    (hB : (carrierBoundaryVertices G
      (offPathComponentCarrier G (rootDeletedComponentCarrier G r C) p E)).card ≤ 1) :
    ∃ t a b c : V,
      offPathComponentCarrier G (rootDeletedComponentCarrier G r C) p E = {t} ∧
      t ∉ p.support ∧ a ∈ p.support ∧ b ∈ p.support ∧ c ∈ p.support ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ G.Adj t a ∧ G.Adj t b ∧ G.Adj t c := by
  classical
  let K := offPathComponentCarrier G (rootDeletedComponentCarrier G r C) p E
  obtain ⟨hK, hKdata, hboundary, _⟩ :=
    cut_side_offPath_carrier_data M r C D hCD hxy hrx hry p hinside E
  have hrK : r ∉ K := fun h =>
    (rootDeletedComponentCarrier_nonempty_not_mem G r C).2 (hKdata r h).1
  obtain ⟨t, ht⟩ := M.carrier_singleton_of_boundary_card_le_one r ⟨C, D, hCD⟩
    K hK hrK hB
  have htK : t ∈ K := by simp [ht]
  have hdegree : 2 < (G.neighborFinset t).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    have h := degree_ge_three_of_minDegree_ge_three G M.isCounterexample.1 t
    omega
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hdegree
  have hta := (G.mem_neighborFinset t a).mp ha
  have htb := (G.mem_neighborFinset t b).mp hb
  have htc := (G.mem_neighborFinset t c).mp hc
  have hout : ∀ w, G.Adj t w → w ∉ K := by
    intro w htw hw
    rw [ht, Finset.mem_singleton] at hw
    exact htw.ne hw.symm
  exact ⟨t, a, b, c, ht, (hKdata t htK).2,
    hboundary t htK a (hout a hta) hta,
    hboundary t htK b (hout b htb) htb,
    hboundary t htK c (hout c htc) htc, hab, hac, hbc, hta, htb, htc⟩

end Erdos64
