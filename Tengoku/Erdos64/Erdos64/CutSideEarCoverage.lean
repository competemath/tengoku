import Tengoku.Erdos64.Erdos64.MinimalCounterexampleUniqueCut
import Tengoku.Erdos64.Erdos64.PathThirdIncidence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- A simple path ending in a set has a simple prefix whose only vertex in
that set is its endpoint. This constructs the first return to a carrier.
@isnad1 id=ex.2h6v.s6.e594bebb6906 from=translated src=- shape=612b96d6 vocab=3f399e93
-/
theorem path_first_hit_set
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hp : p.IsPath) (S : Set V) (hb : b ∈ S) :
    ∃ z, z ∈ S ∧ ∃ q : G.Walk a z,
      q.IsPath ∧ (∀ w, w ∈ q.support → w ∈ p.support) ∧
      (∀ w, w ∈ q.support → w ∈ S → w = z) := by
  classical
  induction p with
  | nil =>
      refine ⟨_, hb, .nil, SimpleGraph.Walk.IsPath.nil, ?_, ?_⟩
      · intro w hw
        exact hw
      · intro w hw _
        simpa using hw
  | @cons a c b hac p ih =>
      by_cases ha : a ∈ S
      · refine ⟨a, ha, .nil, SimpleGraph.Walk.IsPath.nil, ?_, ?_⟩
        · intro w hw
          have : w = a := by simpa using hw
          subst w
          exact SimpleGraph.Walk.start_mem_support _
        · intro w hw _
          simpa using hw
      · obtain ⟨z, hz, q, hq, hsub, hhit⟩ := ih hp.of_cons hb
        have hnot : a ∉ p.support :=
          ((SimpleGraph.Walk.cons_isPath_iff _ _).mp hp).2
        refine ⟨z, hz, q.cons hac, hq.cons (fun h => hnot (hsub a h)), ?_, ?_⟩
        · intro w hw
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hw ⊢
          exact hw.imp_right (hsub w)
        · intro w hw hwS
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hw
          rcases hw with rfl | hw
          · exact (ha hwS).elim
          · exact hhit w hw hwS

/-- A first-hit path remains in a carrier when leaving the carrier would
require passing through the target set first.
@isnad1 id=mem.5h8v.s7.914cf15f35d1 from=translated src=- shape=812c941c vocab=5fc015b5
-/
theorem first_hit_path_support_in_carrier
    {V : Type u} {G : SimpleGraph V} {a z : V}
    (q : G.Walk a z) (hq : q.IsPath) (S D : Set V)
    (ha : a ∈ D)
    (hboundary : ∀ u, u ∈ D → ∀ w, w ∉ D → G.Adj u w → u ∈ S)
    (hhit : ∀ w, w ∈ q.support → w ∈ S → w = z) :
    ∀ w, w ∈ q.support → w ∈ D := by
  induction q with
  | @nil a =>
      intro w hw
      have : w = a := by simpa using hw
      simpa only [this] using ha
  | @cons a b z hab q ih =>
      have hnot : a ∉ q.support :=
        ((SimpleGraph.Walk.cons_isPath_iff _ _).mp hq).2
      have hb : b ∈ D := by
        by_contra hb
        have haS := hboundary a ha b hb hab
        have haz := hhit a (SimpleGraph.Walk.start_mem_support _) haS
        exact hnot (haz.symm ▸ q.end_mem_support)
      have htailhit : ∀ w, w ∈ q.support → w ∈ S → w = z := by
        intro w hw hwS
        exact hhit w (by simp [hw]) hwS
      have htail := ih hq.of_cons hb htailhit
      intro w hw
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact ha
      · exact htail w hw

/-- Connectedness after deleting an attachment turns any external neighbor
into a fresh ear. Carrier closure is checked before the first return.
@isnad1 id=ex.7h8v.s8.4219944f28ab from=translated src=- shape=68fc0a31 vocab=d30fe6b5
-/
theorem fresh_ear_of_external_neighbor
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    {x y v w : V} (p : G.Walk x y) (D : Set V)
    (hconn : (G.induce {a : V | a ≠ v}).Connected)
    (hxv : x ≠ v) (hvw : G.Adj v w)
    (hw : w ∉ p.support) (hvD : v ∈ D) (hwD : w ∈ D)
    (hboundary : ∀ a, a ∈ D → ∀ b, b ∉ D → G.Adj a b → a ∈ p.support) :
    ∃ z, z ∈ p.support ∧ z ≠ v ∧ ∃ ear : G.Walk v z,
      ear.IsPath ∧ 2 ≤ ear.length ∧
      (∀ a, a ∈ ear.support → a ∈ D) ∧
      (∀ a, a ∈ ear.support → a ∈ p.support → a = v ∨ a = z) ∧
      ear.getVert 1 = w ∧ s(v, w) ∉ p.edges := by
  classical
  let ww : {a : V // a ≠ v} := ⟨w, hvw.ne.symm⟩
  let xx : {a : V // a ≠ v} := ⟨x, hxv⟩
  obtain ⟨q, hq⟩ := hconn.exists_isPath ww xx
  let e : G.induce {a : V | a ≠ v} ↪g G := SimpleGraph.Embedding.induce _
  let q' : G.Walk w x := q.map e.toHom
  have hq' : q'.IsPath := hq.map e.injective
  have havoid : ∀ a, a ∈ q'.support → a ≠ v := by
    intro a ha
    change a ∈ (q.map e.toHom).support at ha
    rw [SimpleGraph.Walk.support_map] at ha
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp ha
    exact t.2
  obtain ⟨z, hz, t, ht, hsub, hhit⟩ :=
    path_first_hit_set q' hq' {a | a ∈ p.support} p.start_mem_support
  have hvnot : v ∉ t.support := fun h => havoid v (hsub v h) rfl
  have hzv : z ≠ v := havoid z (hsub z t.end_mem_support)
  have htD : ∀ a, a ∈ t.support → a ∈ D := by
    apply first_hit_path_support_in_carrier t ht {a | a ∈ p.support} D hwD
    · exact hboundary
    · exact hhit
  have htpos : 0 < t.length := by
    by_contra h
    have hwz := SimpleGraph.Walk.eq_of_length_eq_zero (by omega : t.length = 0)
    exact hw (hwz ▸ hz)
  refine ⟨z, hz, hzv, t.cons hvw, ht.cons hvnot, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [SimpleGraph.Walk.length_cons]
    omega
  · intro a ha
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact hvD
    · exact htD a ha
  · intro a ha hap
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at ha
    exact ha.imp_right (fun h => hhit a h hap)
  · simp
  · intro he
    exact hw (p.snd_mem_support_of_mem_edges he)

/-- Every internal vertex of a simple port path in a native cut side has a
fresh ear (possibly a chord) whose first edge is unused by that path. The
minimum-degree hypothesis supplies that edge; unique-cut connectedness
supplies a first return if its other endpoint is outside the path.
@isnad1 id=ex.10h9v.s8.c6df3fb838ac from=translated src=- shape=04314d54 vocab=691f7314
-/
theorem MinimalCounterexample.rootDeleted_cut_side_path_ear_coverage
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (r : V)
    (C D : (G.induce {a : V | a ≠ r}).ConnectedComponent) (hCD : C ≠ D)
    {x y : V} (hxy : x ≠ y) (hrx : G.Adj r x) (hry : G.Adj r y)
    (p : G.Walk x y) (hp : p.IsPath)
    (hinside : ∀ a, a ∈ p.support → a ∈ rootDeletedComponentCarrier G r C)
    (v : V) (hv : v ∈ p.support) (hvx : v ≠ x) (hvy : v ≠ y) :
    ∃ z, z ∈ p.support ∧ z ≠ v ∧ ∃ ear : G.Walk v z,
      ear.IsPath ∧ 1 ≤ ear.length ∧
      (∀ a, a ∈ ear.support → a ∈ rootDeletedComponentCarrier G r C) ∧
      (∀ a, a ∈ ear.support → a ∈ p.support → a = v ∨ a = z) ∧
      s(v, ear.getVert 1) ∉ p.edges := by
  classical
  let := Fintype.ofFinite ((G.induce {a : V | a ≠ r}).ConnectedComponent)
  let A := rootDeletedComponentCarrier G r C
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
  have hports : ∀ a, a ∈ A → G.Adj a r → a = x ∨ a = y := by
    intro a ha har
    have hmem : a ∈ rootDeletedComponentAttachments G r C :=
      Finset.mem_filter.mpr ⟨(G.mem_neighborFinset r a).mpr har.symm, ha⟩
    rw [← hpair] at hmem
    simpa using hmem
  have hboundary : ∀ a, a ∈ A → ∀ b, b ∉ A → G.Adj a b → b = r := by
    intro a ha b hb hab
    exact ((rootDeletedComponent_boundary r M.isConnected C).1 a ha b hab).resolve_left hb
  have hvA : v ∈ A := hinside v hv
  have hvroot : v ≠ r := by
    intro h
    have hrA : r ∈ A := by rw [← h]; exact hvA
    exact (rootDeletedComponentCarrier_nonempty_not_mem G r C).2 hrA
  obtain ⟨w, hvw, hnotedge⟩ := exists_adj_not_mem_path_edges p hp
    (degree_ge_three_of_minDegree_ge_three G M.isCounterexample.1 v)
  have hwA : w ∈ A := by
    by_contra hw
    have hwr := hboundary v hvA w hw hvw
    have hvr : G.Adj v r := hwr ▸ hvw
    exact (hports v hvA hvr).elim hvx hvy
  by_cases hw : w ∈ p.support
  · refine ⟨w, hw, hvw.ne.symm, hvw.toWalk, SimpleGraph.Walk.IsPath.of_adj hvw,
      by simp [SimpleGraph.Adj.toWalk], ?_, ?_, ?_⟩
    · intro a ha
      simp [SimpleGraph.Adj.toWalk] at ha
      rcases ha with rfl | rfl
      · exact hvA
      · exact hwA
    · intro a ha _
      simpa [SimpleGraph.Adj.toWalk] using ha
    · simpa [SimpleGraph.Adj.toWalk] using hnotedge
  · have hconn := M.rootDeleted_connected_away_from_cut r v ⟨C, D, hCD⟩ hvroot
    have hreturn : ∀ a, a ∈ (↑A : Set V) → ∀ b, b ∉ (↑A : Set V) →
        G.Adj a b → a ∈ p.support := by
      intro a ha b hb hab
      have hbr := hboundary a ha b hb hab
      rcases hports a ha (hbr ▸ hab) with rfl | rfl
      · exact p.start_mem_support
      · exact p.end_mem_support
    obtain ⟨z, hz, hzv, ear, hear, hlen, hearA, hfresh, hfirst, hnot⟩ :=
      fresh_ear_of_external_neighbor p (↑A : Set V) hconn hvx.symm hvw hw hvA hwA hreturn
    refine ⟨z, hz, hzv, ear, hear, by omega, hearA, hfresh, ?_⟩
    simpa only [hfirst] using hnot

end Erdos64
