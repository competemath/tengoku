import Tengoku.Erdos64.Erdos64.TwoStepCycleLift
import Tengoku.Erdos64.Erdos64.SharedRootQuotientResidual

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Vertices whose degree is strictly above the minimum-degree threshold.-/
abbrev HighDegreeVertex := {v : V // 4 ≤ G.degree v}

/-- The auxiliary graph joins two high-degree vertices when they share a
cubic neighbor.-/
def highDegreeAuxGraph : SimpleGraph (HighDegreeVertex G) where
  Adj x y := x ≠ y ∧ ∃ v, G.degree v = 3 ∧ G.Adj v x.1 ∧ G.Adj v y.1
  symm := ⟨by
    rintro x y ⟨hne, v, hv, hx, hy⟩
    exact ⟨hne.symm, v, hv, hy, hx⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

noncomputable instance highDegreeAuxGraphDecidableAdj :
    DecidableRel (highDegreeAuxGraph G).Adj := Classical.decRel _

/-- High-degree neighbors of an ambient vertex.-/
def highDegreeNeighbors (v : V) : Finset V :=
  (Finset.univ.filter (fun w => 4 ≤ G.degree w)).filter (G.Adj v)

/-- Cubic vertices having exactly two high-degree neighbors.-/
def degreeThreeTwoHighNeighbors : Finset V :=
  (Finset.univ.filter (fun v => G.degree v = 3)).filter
    (fun v => (highDegreeNeighbors G v).card = 2)

omit [DecidableEq V] in
theorem highDegreeAuxGraph_edge_has_connector (e : (highDegreeAuxGraph G).edgeSet) :
    ∃ v, G.degree v = 3 ∧ ∀ x ∈ e.1, G.Adj v x.1 := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
    obtain ⟨_, v, hv, hx, hy⟩ := he
    refine ⟨v, hv, ?_⟩
    intro z hz
    rcases Sym2.mem_iff.mp hz with rfl | rfl
    · exact hx
    · exact hy

/-- The chosen cubic connector for an auxiliary edge. Uniqueness is proved below.-/
noncomputable def highDegreeConnector (e : (highDegreeAuxGraph G).edgeSet) : V :=
  Classical.choose (highDegreeAuxGraph_edge_has_connector G e)

omit [DecidableEq V] in
theorem highDegreeConnector_spec (e : (highDegreeAuxGraph G).edgeSet) :
    G.degree (highDegreeConnector G e) = 3 ∧
      ∀ x ∈ e.1, G.Adj (highDegreeConnector G e) x.1 :=
  Classical.choose_spec (highDegreeAuxGraph_edge_has_connector G e)

variable {G}

/-- Two common neighbors of distinct high-degree vertices coincide: otherwise
the four vertices give a forbidden 4-cycle.-/
theorem EdgeMinimalCounterexample.highDegreeAuxGraph_connector_unique
    (M : EdgeMinimalCounterexample G) {x y : HighDegreeVertex G}
    (hxy : x ≠ y) {v w : V}
    (hvx : G.Adj v x.1) (hvy : G.Adj v y.1)
    (hwx : G.Adj w x.1) (hwy : G.Adj w y.1) : v = w := by
  exact (M.vertexMinimal.common_neighbor_eq_root_of_nonadjacent_ports
    hvx hvy (fun h => hxy (Subtype.ext h)) hwx.symm hwy.symm hwx.ne hwy.ne).symm

/-- The two endpoints exhaust the high-degree neighbors of a cubic connector.-/
theorem EdgeMinimalCounterexample.highDegreeNeighbors_eq_pair
    (M : EdgeMinimalCounterexample G) {v : V} (hv : G.degree v = 3)
    {x y : HighDegreeVertex G} (hxy : x ≠ y)
    (hx : G.Adj v x.1) (hy : G.Adj v y.1) :
    highDegreeNeighbors G v = {x.1, y.1} := by
  have hxy' : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
  have hsub : ({x.1, y.1} : Finset V) ⊆ highDegreeNeighbors G v := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · simp [highDegreeNeighbors, x.2, hx]
    · simp [highDegreeNeighbors, y.2, hy]
  have hcard := M.high_degree_neighborFinset_card_le_two_of_degree_eq_three hv
  apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
  simpa [highDegreeNeighbors, hxy'] using hcard

theorem EdgeMinimalCounterexample.highDegreeConnector_injective
    (M : EdgeMinimalCounterexample G) : Function.Injective (highDegreeConnector G) := by
  intro e d heq
  rcases e with ⟨e, he⟩
  rcases d with ⟨d, hd⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
    induction d using Sym2.inductionOn with
    | _ z w =>
      have hxy := (highDegreeConnector_spec G ⟨s(x, y), he⟩)
      have hzw := (highDegreeConnector_spec G ⟨s(z, w), hd⟩)
      have hp := M.highDegreeNeighbors_eq_pair hxy.1 he.1
        (hxy.2 x (by simp)) (hxy.2 y (by simp))
      have hq := M.highDegreeNeighbors_eq_pair hzw.1 hd.1
        (hzw.2 z (by simp)) (hzw.2 w (by simp))
      rw [heq] at hp
      have hpq : ({x.1, y.1} : Finset V) = {z.1, w.1} := hp.symm.trans hq
      apply Subtype.ext
      apply Sym2.ext
      intro a
      have hmem := congrArg (fun S : Finset V => a.1 ∈ S) hpq
      simpa only [Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton,
        Subtype.ext_iff] using eq_iff_iff.mp hmem

/-- The auxiliary graph is realized inside the ambient graph by subdividing
every edge once at its unique cubic connector.-/
noncomputable def EdgeMinimalCounterexample.highDegreeTwoStepEmbedding
    (M : EdgeMinimalCounterexample G) : TwoStepEmbedding (highDegreeAuxGraph G) G where
  vertex := ⟨Subtype.val, Subtype.val_injective⟩
  middle := ⟨highDegreeConnector G, M.highDegreeConnector_injective⟩
  disjoint := by
    intro x e heq
    have hx := x.2
    have he := (highDegreeConnector_spec G e).1
    change x.1 = highDegreeConnector G e at heq
    rw [heq, he] at hx
    omega
  adj := by
    intro x y h
    have hs := (highDegreeConnector_spec G ⟨s(x, y), h⟩).2
    exact ⟨(hs x (by simp)).symm, hs y (by simp)⟩

theorem EdgeMinimalCounterexample.highDegreeAuxGraph_no_dyadic_cycle
    (M : EdgeMinimalCounterexample G) : ¬HasPowerOfTwoCycle (highDegreeAuxGraph G) := by
  intro h
  exact M.vertexMinimal.isCounterexample.2 (M.highDegreeTwoStepEmbedding.hasPowerOfTwoCycle h)

theorem EdgeMinimalCounterexample.highDegreeVertex_card_lt
    (M : EdgeMinimalCounterexample G) : Fintype.card (HighDegreeVertex G) < Fintype.card V := by
  obtain ⟨v, hv⟩ := M.exists_degree_eq_three
  have hc : G.degree v = 3 := (Finset.mem_filter.mp hv).2
  exact Fintype.card_subtype_lt (x := v) (by omega)

theorem EdgeMinimalCounterexample.highDegreeConnector_mem_degreeThreeTwoHighNeighbors
    (M : EdgeMinimalCounterexample G) (e : (highDegreeAuxGraph G).edgeSet) :
    highDegreeConnector G e ∈ degreeThreeTwoHighNeighbors G := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
    have hs := highDegreeConnector_spec G ⟨s(x, y), he⟩
    have hn := M.highDegreeNeighbors_eq_pair hs.1 he.1
      (hs.2 x (by simp)) (hs.2 y (by simp))
    have hne : x.1 ≠ y.1 := fun h => he.1 (Subtype.ext h)
    simp [degreeThreeTwoHighNeighbors, hs.1, hn, hne]

/-- The chosen connectors are exactly the cubic vertices with two high-degree
neighbors; the no-4-cycle condition makes each choice canonical.-/
theorem EdgeMinimalCounterexample.highDegreeConnector_range_iff
    (M : EdgeMinimalCounterexample G) (v : V) :
    (∃ e, highDegreeConnector G e = v) ↔ v ∈ degreeThreeTwoHighNeighbors G := by
  constructor
  · rintro ⟨e, rfl⟩
    exact M.highDegreeConnector_mem_degreeThreeTwoHighNeighbors e
  · intro hv
    have hdeg : G.degree v = 3 := (Finset.mem_filter.mp
      (Finset.mem_filter.mp hv).1).2
    have hcard : (highDegreeNeighbors G v).card = 2 := (Finset.mem_filter.mp hv).2
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (show
      1 < (highDegreeNeighbors G v).card by omega)
    have hx' : 4 ≤ G.degree x ∧ G.Adj v x := by simpa [highDegreeNeighbors] using hx
    have hy' : 4 ≤ G.degree y ∧ G.Adj v y := by simpa [highDegreeNeighbors] using hy
    let X : HighDegreeVertex G := ⟨x, hx'.1⟩
    let Y : HighDegreeVertex G := ⟨y, hy'.1⟩
    have hXY : X ≠ Y := fun h => hxy (congrArg Subtype.val h)
    have hedge : (highDegreeAuxGraph G).Adj X Y := ⟨hXY, v, hdeg, hx'.2, hy'.2⟩
    let e : (highDegreeAuxGraph G).edgeSet := ⟨s(X, Y), hedge⟩
    refine ⟨e, ?_⟩
    have hs := highDegreeConnector_spec G e
    exact M.highDegreeAuxGraph_connector_unique hXY
      (hs.2 X (by simp [e])) (hs.2 Y (by simp [e])) hx'.2 hy'.2

/-- Count auxiliary edges by their unique cubic subdivision vertices.-/
theorem EdgeMinimalCounterexample.highDegreeAuxGraph_edge_card
    (M : EdgeMinimalCounterexample G) :
    Fintype.card (highDegreeAuxGraph G).edgeSet = (degreeThreeTwoHighNeighbors G).card := by
  classical
  let f : (highDegreeAuxGraph G).edgeSet → (degreeThreeTwoHighNeighbors G) :=
    fun e => ⟨highDegreeConnector G e, M.highDegreeConnector_mem_degreeThreeTwoHighNeighbors e⟩
  have hf : Function.Bijective f := by
    constructor
    · intro e d h
      exact M.highDegreeConnector_injective (congrArg Subtype.val h)
    · intro v
      obtain ⟨e, he⟩ := (M.highDegreeConnector_range_iff v.1).2 v.2
      exact ⟨e, Subtype.ext he⟩
  exact (Fintype.card_congr (Equiv.ofBijective f hf)).trans (Fintype.card_coe _)

/-- Auxiliary degree counts exactly the adjacent cubic vertices with two
high-degree neighbors.-/
theorem EdgeMinimalCounterexample.highDegreeAuxGraph_degree_eq_connector_count
    (M : EdgeMinimalCounterexample G) (x : HighDegreeVertex G) :
    (highDegreeAuxGraph G).degree x =
      ((degreeThreeTwoHighNeighbors G).filter (G.Adj x.1)).card := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  let edgeOf : ∀ y, y ∈ (highDegreeAuxGraph G).neighborFinset x →
      (highDegreeAuxGraph G).edgeSet :=
    fun y hy => ⟨s(x, y), by simpa using hy⟩
  apply Finset.card_bij (fun y hy => highDegreeConnector G (edgeOf y hy))
  · intro y hy
    refine Finset.mem_filter.mpr
      ⟨M.highDegreeConnector_mem_degreeThreeTwoHighNeighbors _, ?_⟩
    exact ((highDegreeConnector_spec G (edgeOf y hy)).2 x (by simp [edgeOf])).symm
  · intro y hy z hz heq
    have he := congrArg Subtype.val (M.highDegreeConnector_injective heq)
    change s(x, y) = s(x, z) at he
    rcases Sym2.eq_iff.mp he with h | h
    · exact h.2
    · exact h.2.trans h.1
  · intro v hv
    have hL := (Finset.mem_filter.mp hv).1
    have hxv := (Finset.mem_filter.mp hv).2
    have hdeg : G.degree v = 3 := (Finset.mem_filter.mp
      (Finset.mem_filter.mp hL).1).2
    have hcard : (highDegreeNeighbors G v).card = 2 := (Finset.mem_filter.mp hL).2
    obtain ⟨y, hy, hyx⟩ := Finset.exists_mem_ne (show
      1 < (highDegreeNeighbors G v).card by omega) x.1
    have hy' : 4 ≤ G.degree y ∧ G.Adj v y := by simpa [highDegreeNeighbors] using hy
    let Y : HighDegreeVertex G := ⟨y, hy'.1⟩
    have hXY : x ≠ Y := fun h => hyx (congrArg Subtype.val h).symm
    have hedge : (highDegreeAuxGraph G).Adj x Y :=
      ⟨hXY, v, hdeg, hxv.symm, hy'.2⟩
    have hY : Y ∈ (highDegreeAuxGraph G).neighborFinset x :=
      by simpa using hedge
    refine ⟨Y, hY, ?_⟩
    have hs := highDegreeConnector_spec G (edgeOf Y hY)
    exact M.highDegreeAuxGraph_connector_unique hXY
      (hs.2 x (by simp [edgeOf])) (hs.2 Y (by simp [edgeOf])) hxv.symm hy'.2

end Erdos64
