import Tengoku.Erdos64.Erdos64.CutSideDyadicEarAvoidance
import Tengoku.Erdos64.Erdos64.TwoPortEdgeCompletion
import Tengoku.Erdos64.Erdos64.AddedEdgeCyclePath

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

private theorem extend_carrier_path_to_external_ear
    {V : Type u} {G : SimpleGraph V} {u v a b : V}
    (K : Finset V) (ha : a ∉ K) (hb : b ∉ K) (hab : a ≠ b)
    (hua : G.Adj u a) (hvb : G.Adj v b)
    (q : G.Walk u v) (hq : q.IsPath)
    (hqK : ∀ z, z ∈ q.support → z ∈ K) :
    ∃ ear : G.Walk a b, ear.IsPath ∧ ear.length = q.length + 2 ∧
      (∀ z, z ∈ ear.support → z = a ∨ z = b ∨ z ∈ K) := by
  have haavoid : a ∉ q.support := fun h => ha (hqK a h)
  have hbavoid : b ∉ q.support := fun h => hb (hqK b h)
  let ear := (q.cons hua.symm).concat hvb
  refine ⟨ear, ?_, ?_, ?_⟩
  · apply SimpleGraph.Walk.IsPath.concat (hq.cons haavoid)
    simp [hbavoid, hab.symm]
  · simp [ear, Nat.add_assoc]
  · intro z hz
    simp only [ear, SimpleGraph.Walk.support_concat, SimpleGraph.Walk.support_cons,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (hqK z h))
    · exact Or.inr (Or.inl h)

/-- A small carrier with exactly two crossing edges supplies a dyadic ear
between their specified distinct external endpoints. The endpoints are
fixed, rather than independently selected by a generic ear theorem.-/
theorem MinimalCounterexample.exact_two_crossing_edges_dyadic_ear
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (K : Finset V)
    (u v a b : V) (hu : u ∈ K) (ha : a ∉ K) (hb : b ∉ K) (hab : a ≠ b)
    (hboundary : ∀ z, z ∈ K → ∀ w, w ∉ K → G.Adj z w →
      (z = u ∧ w = a) ∨ (z = v ∧ w = b))
    (hsize : 2 * K.card + 1 < Fintype.card V) :
    ∃ k : ℕ, ∃ ear : G.Walk a b,
      1 ≤ k ∧ ear.IsPath ∧ ear.length = 2 ^ k ∧
      (∀ z, z ∈ ear.support → z = a ∨ z = b ∨ z ∈ K) := by
  have hdisjoint : ∀ z, z ∈ K → z ∉ ({w | w = a ∨ w = b} : Set V) := by
    intro z hz h
    rcases h with rfl | rfl
    · exact ha hz
    · exact hb hz
  have hbound : ∀ z, z ∈ K → ∀ w, w ∉ K → G.Adj z w →
      w ∈ ({z | z = a ∨ z = b} : Set V) := by
    intro z hz w hw hzw
    exact (hboundary z hz w hw hzw).imp And.right And.right
  obtain ⟨k, c, d, q, hk, hc, hd, hcd, hq, hlen, hsupport, _⟩ :=
    M.small_carrier_dyadic_ear K {z | z = a ∨ z = b} ⟨u, hu⟩
      hdisjoint hbound hsize
  rcases hc with hca | hcb <;> rcases hd with hda | hdb
  · exact (hcd (hca.trans hda.symm)).elim
  · subst c
    subst d
    exact ⟨k, q, hk, hq, hlen, hsupport⟩
  · subst c
    subst d
    refine ⟨k, q.reverse, hk, hq.reverse, ?_, ?_⟩
    · simpa only [SimpleGraph.Walk.length_reverse] using hlen
    · intro z hz
      have hz' : z ∈ q.support := by simpa using hz
      rcases hsupport z hz' with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  · exact (hcd (hcb.trans hdb.symm)).elim

/-- Completing the two internal boundary vertices by an edge supplies an
odd ear with the same two external attachments. If the internal edge already
exists, the three-edge ear gives exponent one directly.-/
theorem MinimalCounterexample.exact_two_crossing_edges_dyadic_successor_ear
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (K : Finset V)
    (u v a b : V) (hu : u ∈ K) (hv : v ∈ K) (huv : u ≠ v)
    (ha : a ∉ K) (hb : b ∉ K) (hab : a ≠ b)
    (hua : G.Adj u a) (hvb : G.Adj v b)
    (hboundary : ∀ z, z ∈ K → ∀ w, w ∉ K → G.Adj z w →
      (z = u ∧ w = a) ∨ (z = v ∧ w = b))
    (hsize : K.card < Fintype.card V) :
    ∃ k : ℕ, ∃ ear : G.Walk a b,
      1 ≤ k ∧ ear.IsPath ∧ ear.length = 2 ^ k + 1 ∧
      (∀ z, z ∈ ear.support → z = a ∨ z = b ∨ z ∈ K) := by
  classical
  by_cases huvAdj : G.Adj u v
  · obtain ⟨ear, hear, hlen, hsupport⟩ := extend_carrier_path_to_external_ear
      K ha hb hab hua hvb huvAdj.toWalk (SimpleGraph.Walk.IsPath.of_adj huvAdj)
      (by intro z hz; simp [SimpleGraph.Adj.toWalk] at hz; rcases hz with rfl | rfl
          · exact hu
          · exact hv)
    exact ⟨1, ear, by omega, hear, by simpa using hlen, hsupport⟩
  have hsingle : ∀ z, z ∈ K → ∀ c, c ∉ K → ∀ d, d ∉ K →
      G.Adj z c → G.Adj z d → c = d := by
    intro z hz c hc d hd hzc hzd
    have hc' := hboundary z hz c hc hzc
    have hd' := hboundary z hz d hd hzd
    rcases hc' with ⟨hzu, hca⟩ | ⟨hzv, hcb⟩
    · rcases hd' with ⟨_, hda⟩ | ⟨hzv, _⟩
      · exact hca.trans hda.symm
      · exact (huv (hzu.symm.trans hzv)).elim
    · rcases hd' with ⟨hzu, _⟩ | ⟨_, hdb⟩
      · exact (huv (hzu.symm.trans hzv)).elim
      · exact hcb.trans hdb.symm
  let H := G.induce (↑K : Set V)
  let uu : (↑K : Set V) := ⟨u, hu⟩
  let vv : (↑K : Set V) := ⟨v, hv⟩
  have huuvv : uu ≠ vv := fun h => huv (congrArg Subtype.val h)
  have hB : ∀ z : (↑K : Set V),
      z ∈ carrierBoundaryVertices G K ↔ z = uu ∨ z = vv := by
    intro z
    rw [mem_carrierBoundaryVertices]
    constructor
    · rintro ⟨w, hw, hzw⟩
      rcases hboundary z.1 z.2 w hw hzw with h | h
      · exact Or.inl (Subtype.ext h.1)
      · exact Or.inr (Subtype.ext h.1)
    · rintro (rfl | rfl)
      · exact ⟨a, ha, hua⟩
      · exact ⟨b, hb, hvb⟩
  let J := H ⊔ SimpleGraph.edge uu vv
  have hdeg : ∀ z, J.degree z = G.degree z.1 := by
    intro z
    rw [degree_sup_edge_of_not_adj H huuvv huvAdj]
    have h := carrier_degree_add_boundary_indicator K hsingle z
    simpa only [hB z] using h
  have hyes : HasPowerOfTwoCycle J := by
    by_contra hno
    have hmin : 3 ≤ J.minDegree := by
      let : Nonempty (↑K : Set V) := ⟨uu⟩
      apply J.le_minDegree_of_forall_le_degree
      intro z
      rw [hdeg]
      exact degree_ge_three_of_minDegree_ge_three G M.isCounterexample.1 z.1
    have hsmall : Fintype.card (↑K : Set V) < Fintype.card V := by simpa using hsize
    exact M.not_exists_strictly_smaller (H := J) ⟨⟨hmin, hno⟩, hsmall⟩
  have hHno : ¬HasPowerOfTwoCycle H :=
    not_hasPowerOfTwoCycle_induce_of_not_hasPowerOfTwoCycle M.isCounterexample.2
  obtain ⟨k, q, hk, hq, hlen⟩ := added_edge_dyadic_cycle_path hHno hyes
  let e : H ↪g G := SimpleGraph.Embedding.induce (↑K : Set V)
  let q' : G.Walk u v := q.map e.toHom
  have hq' : q'.IsPath := hq.map e.injective
  have hqK : ∀ z, z ∈ q'.support → z ∈ K := by
    intro z hz
    change z ∈ (q.map e.toHom).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz
    exact w.2
  obtain ⟨ear, hear, hearlength, hsupport⟩ :=
    extend_carrier_path_to_external_ear K ha hb hab hua hvb q' hq' hqK
  have hqlength : q'.length + 1 = 2 ^ k := by
    change (q.map e.toHom).length + 1 = 2 ^ k
    rw [SimpleGraph.Walk.length_map]
    exact hlen
  exact ⟨k, ear, by omega, hear, by omega, hsupport⟩

/-- Both parities are forced at the same attachment pair for a small region
whose entire boundary consists of the two specified crossing edges.-/
theorem MinimalCounterexample.exact_two_crossing_edges_ear_spectrum
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (K : Finset V)
    (u v a b : V) (hu : u ∈ K) (hv : v ∈ K) (huv : u ≠ v)
    (ha : a ∉ K) (hb : b ∉ K) (hab : a ≠ b)
    (hua : G.Adj u a) (hvb : G.Adj v b)
    (hboundary : ∀ z, z ∈ K → ∀ w, w ∉ K → G.Adj z w →
      (z = u ∧ w = a) ∨ (z = v ∧ w = b))
    (hsize : 2 * K.card + 1 < Fintype.card V) :
    ∃ i j : ℕ, ∃ evenEar oddEar : G.Walk a b,
      1 ≤ i ∧ 1 ≤ j ∧ evenEar.IsPath ∧ oddEar.IsPath ∧
      evenEar.length = 2 ^ i ∧ oddEar.length = 2 ^ j + 1 ∧
      (∀ z, z ∈ evenEar.support → z = a ∨ z = b ∨ z ∈ K) ∧
      (∀ z, z ∈ oddEar.support → z = a ∨ z = b ∨ z ∈ K) := by
  obtain ⟨i, evenEar, hi, heven, helen, hesupport⟩ :=
    M.exact_two_crossing_edges_dyadic_ear K u v a b hu ha hb hab hboundary hsize
  obtain ⟨j, oddEar, hj, hodd, holen, hosupport⟩ :=
    M.exact_two_crossing_edges_dyadic_successor_ear K u v a b hu hv huv ha hb hab
      hua hvb hboundary (by omega)
  exact ⟨i, j, evenEar, oddEar, hi, hj, heven, hodd, helen, holen, hesupport, hosupport⟩

/-- Two boundary vertices need not mean two crossing edges. A component
outside a cubic port path therefore has an honest split: one internal vertex
already supplies a two-edge fork, or the boundary consists of two crossing
edges and both dyadic and dyadic-successor ears use their same fixed external
attachments. No relation between the two exponents is asserted.-/
theorem MinimalCounterexample.rootDeleted_two_boundary_component_fork_or_ear_spectrum
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (r : V)
    (C D : (G.induce {v : V | v ≠ r}).ConnectedComponent) (hCD : C ≠ D)
    {x y : V} (hxy : x ≠ y) (hrx : G.Adj r x) (hry : G.Adj r y)
    (p : G.Walk x y) (hp : p.IsPath)
    (hinside : ∀ z, z ∈ p.support → z ∈ rootDeletedComponentCarrier G r C)
    (hcubic : ∀ z, z ∈ p.support → G.degree z = 3)
    (E : (G.induce {z : V | z ∈ rootDeletedComponentCarrier G r C ∧
      z ∉ p.support}).ConnectedComponent)
    (hB : (carrierBoundaryVertices G
      (offPathComponentCarrier G (rootDeletedComponentCarrier G r C) p E)).card = 2) :
    let K := offPathComponentCarrier G (rootDeletedComponentCarrier G r C) p E
    (∃ u a b : V, ∃ ear : G.Walk a b,
      u ∈ K ∧ a ∈ p.support ∧ b ∈ p.support ∧ a ≠ b ∧
      G.Adj u a ∧ G.Adj u b ∧ ear.IsPath ∧ ear.length = 2 ∧
      (∀ z, z ∈ ear.support → z = a ∨ z = b ∨ z ∈ K)) ∨
    (∃ u v a b : V,
      u ∈ K ∧ v ∈ K ∧ u ≠ v ∧ a ∈ p.support ∧ b ∈ p.support ∧ a ≠ b ∧
      G.Adj u a ∧ G.Adj v b ∧
      (∀ z, z ∈ K → ∀ w, w ∉ K → G.Adj z w →
        (z = u ∧ w = a) ∨ (z = v ∧ w = b)) ∧
      ∃ i j : ℕ, ∃ evenEar oddEar : G.Walk a b,
        1 ≤ i ∧ 1 ≤ j ∧ evenEar.IsPath ∧ oddEar.IsPath ∧
        evenEar.length = 2 ^ i ∧ oddEar.length = 2 ^ j + 1 ∧
        (∀ z, z ∈ evenEar.support → z = a ∨ z = b ∨ z ∈ K) ∧
        (∀ z, z ∈ oddEar.support → z = a ∨ z = b ∨ z ∈ K)) := by
  classical
  let K := offPathComponentCarrier G (rootDeletedComponentCarrier G r C) p E
  obtain ⟨_, hKdata, hboundary, hsize⟩ :=
    cut_side_offPath_carrier_data M r C D hCD hxy hrx hry p hinside E
  by_cases htwo : ∃ z ∈ K, ∃ a, a ∉ K ∧ ∃ b, b ∉ K ∧
      a ≠ b ∧ G.Adj z a ∧ G.Adj z b
  · obtain ⟨u, hu, a, ha, b, hb, hab, hua, hub⟩ := htwo
    let ear : G.Walk a b := .cons hua.symm (.cons hub .nil)
    have hear : ear.IsPath := by
      apply SimpleGraph.Walk.IsPath.cons (SimpleGraph.Walk.IsPath.of_adj hub)
      simp [hua.ne.symm, hab]
    left
    refine ⟨u, a, b, ear, hu, hboundary u hu a ha hua,
      hboundary u hu b hb hub, hab, hua, hub, hear, rfl, ?_⟩
    intro z hz
    simp only [ear, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (h ▸ hu))
    · exact Or.inr (Or.inl h)
  have hsingle : ∀ z, z ∈ K → ∀ a, a ∉ K → ∀ b, b ∉ K →
      G.Adj z a → G.Adj z b → a = b := by
    intro z hz a ha b hb hza hzb
    by_contra hab
    exact htwo ⟨z, hz, a, ha, b, hb, hab, hza, hzb⟩
  obtain ⟨u, v, huv, hBeq⟩ := Finset.card_eq_two.mp hB
  have huB : u ∈ carrierBoundaryVertices G K := by rw [hBeq]; simp
  have hvB : v ∈ carrierBoundaryVertices G K := by rw [hBeq]; simp
  obtain ⟨a, ha, hua⟩ := (mem_carrierBoundaryVertices G K u).mp huB
  obtain ⟨b, hb, hvb⟩ := (mem_carrierBoundaryVertices G K v).mp hvB
  have haP : a ∈ p.support := hboundary u.1 u.2 a ha hua
  have hbP : b ∈ p.support := hboundary v.1 v.2 b hb hvb
  have hab : a ≠ b := by
    intro h
    have hvb' : G.Adj v.1 a := h ▸ hvb
    have hvals := cut_side_port_path_external_neighbors_eq r C hxy hrx hry p hp hinside
      K hKdata a haP (hcubic a haP) u.1 u.2 v.1 v.2 hua.symm hvb'.symm
    exact huv (Subtype.ext hvals)
  have hbound : ∀ z, z ∈ K → ∀ w, w ∉ K → G.Adj z w →
      (z = u.1 ∧ w = a) ∨ (z = v.1 ∧ w = b) := by
    intro z hz w hw hzw
    have hzB : (⟨z, hz⟩ : (↑K : Set V)) ∈ carrierBoundaryVertices G K :=
      (mem_carrierBoundaryVertices G K ⟨z, hz⟩).mpr ⟨w, hw, hzw⟩
    rw [hBeq] at hzB
    rcases Finset.mem_insert.mp hzB with hzu | hzv
    · have hzu : z = u.1 := congrArg Subtype.val hzu
      exact Or.inl ⟨hzu, hsingle z hz w hw a ha hzw (hzu.symm ▸ hua)⟩
    · have hzv : z = v.1 := congrArg Subtype.val (Finset.mem_singleton.mp hzv)
      exact Or.inr ⟨hzv, hsingle z hz w hw b hb hzw (hzv.symm ▸ hvb)⟩
  have huv' : u.1 ≠ v.1 := fun h => huv (Subtype.ext h)
  right
  refine ⟨u.1, v.1, a, b, u.2, v.2, huv', haP, hbP, hab, hua, hvb, hbound, ?_⟩
  exact M.exact_two_crossing_edges_ear_spectrum K u.1 v.1 a b
    u.2 v.2 huv' ha hb hab hua hvb hbound hsize

end Erdos64
