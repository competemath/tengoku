import Tengoku.Linearhadwiger.HadwigerLean.Graph.DensityConnectivity
import Tengoku.Linearhadwiger.HadwigerLean.Graph.ContractionEdges
import Tengoku.Seed.Combinatorics.SimpleGraph.DeleteEdges
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The dense-minor reduction

Appendix E first replaces a dense finite graph by a minor with minimum
`vertex count + edge count` among minors meeting the same integer density
threshold. This module records that extremal choice and its immediate
edge-minimal consequences.
-/

namespace HadwigerLean

universe u

variable {V : Type u} [Fintype V]

/-- A graph obtained by removing edges is a minor, via singleton branches.
@isnad1 id=isminor.1h3v.s4.39f73964e7b8 from=translated src=- shape=8156789a vocab=7627e32e
-/
theorem isMinor_of_graph_le {G H : SimpleGraph V} (h : H ≤ G) : IsMinor H G :=
  ⟨(MinorModel.refl H).mono h⟩

/-- A graph induced on a vertex set is a minor of the ambient graph.
@isnad1 id=isminor.0h3v.s4.80346985a6ad from=translated src=- shape=764d28da vocab=6c48dca3
-/
theorem induce_isMinor (G : SimpleGraph V) (S : Set V) : IsMinor (G.induce S) G :=
  ⟨(MinorModel.refl (G.induce S)).map
    (SimpleGraph.Embedding.induce S).toHom Subtype.coe_injective⟩

private def DenseMinorScore (G : SimpleGraph V) (d score : ℕ) : Prop :=
  ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W),
    IsMinor H G ∧ 0 < Fintype.card W ∧ d * Fintype.card W ≤ edgeCount H ∧
      Fintype.card W + edgeCount H = score

/-- There is a dense minor minimizing the sum of its vertex and edge counts.
@isnad1 id=ex.2h3v.s7.09b73d762289 from=translated src=- shape=325dd837 vocab=80f528cc
-/
theorem exists_minimal_dense_minor (G : SimpleGraph V) (d : ℕ)
    (hnonempty : 0 < Fintype.card V)
    (hdense : d * Fintype.card V ≤ edgeCount G) :
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W),
      IsMinor H G ∧ 0 < Fintype.card W ∧ d * Fintype.card W ≤ edgeCount H ∧
      (∀ {X : Type u} [Fintype X] (J : SimpleGraph X),
        IsMinor J G → 0 < Fintype.card X → d * Fintype.card X ≤ edgeCount J →
        Fintype.card W + edgeCount H ≤ Fintype.card X + edgeCount J) := by
  classical
  let P : ℕ → Prop := DenseMinorScore G d
  have hP : ∃ score, P score := by
    refine ⟨Fintype.card V + edgeCount G, V, inferInstance, G,
      IsMinor.refl G, hnonempty, hdense, rfl⟩
  obtain ⟨W, instW, H, hminor, hpositive, hden, hscore⟩ := Nat.find_spec hP
  letI : Fintype W := instW
  refine ⟨W, instW, H, hminor, hpositive, hden, ?_⟩
  intro X instX J hJG hJpositive hJdense
  letI : Fintype X := instX
  have hJ : P (Fintype.card X + edgeCount J) :=
    ⟨X, instX, J, hJG, hJpositive, hJdense, rfl⟩
  calc
    Fintype.card W + edgeCount H = Nat.find hP := hscore
    _ ≤ Fintype.card X + edgeCount J := Nat.find_min' hP hJ

/-- Deleting one present edge removes exactly one edge.
@isnad1 id=eq.1h3v.s6.253a2e9aca75 from=translated src=- shape=ac3e577b vocab=5ef57003
-/
theorem edgeCount_delete_one [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    edgeCount (G.deleteEdges ({e} : Finset (Sym2 V))) + 1 = edgeCount G := by
  classical
  rw [edgeCount_eq_card_edgeFinset, edgeCount_eq_card_edgeFinset,
    G.edgeFinset_deleteEdges]
  rw [Finset.sdiff_singleton_eq_erase]
  exact Finset.card_erase_add_one he

/-- A positive-order dense minor of minimum score has exactly `d` edges per
vertex; otherwise one edge can be deleted while preserving the inequality.
@isnad1 id=ex.2h3v.s7.19742427a4f5 from=translated src=- shape=dca388fc vocab=80f528cc
-/
theorem exists_edge_exact_dense_minor (G : SimpleGraph V) (d : ℕ)
    (hnonempty : 0 < Fintype.card V)
    (hdense : d * Fintype.card V ≤ edgeCount G) :
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W),
      IsMinor H G ∧ 0 < Fintype.card W ∧ edgeCount H = d * Fintype.card W ∧
      (∀ {X : Type u} [Fintype X] (J : SimpleGraph X),
        IsMinor J G → 0 < Fintype.card X → d * Fintype.card X ≤ edgeCount J →
        Fintype.card W + edgeCount H ≤ Fintype.card X + edgeCount J) := by
  classical
  obtain ⟨W, instW, H, hminor, hpositive, hden, hmin⟩ :=
    exists_minimal_dense_minor G d hnonempty hdense
  letI : Fintype W := instW
  have hexact : edgeCount H = d * Fintype.card W := by
    by_contra hne
    have hstrict : d * Fintype.card W < edgeCount H := by omega
    have hpositiveEdge : 0 < H.edgeFinset.card := by
      rw [← edgeCount_eq_card_edgeFinset]
      omega
    obtain ⟨e, he⟩ := Finset.card_pos.mp hpositiveEdge
    let J := H.deleteEdges ({e} : Finset (Sym2 W))
    have hJminorH : IsMinor J H := isMinor_of_graph_le (H.deleteEdges_le _)
    have hJminorG : IsMinor J G := IsMinor.trans hJminorH hminor
    have hJbalance : edgeCount J + 1 = edgeCount H := edgeCount_delete_one H e he
    have hJdense : d * Fintype.card W ≤ edgeCount J := by omega
    have hMinJ := hmin J hJminorG hpositive hJdense
    omega
  exact ⟨W, instW, H, hminor, hpositive, hexact, hmin⟩

/-- A minimum-score positive-order dense minor has no isolated vertex.
Deleting such a vertex would preserve the density inequality and reduce the
score.
@isnad1 id=lt.5h6v.s7.ae5edb7bfb35 from=translated src=- shape=26eaff1d vocab=1652a774
-/
theorem no_isolated_of_minimal_dense_minor {W : Type u} [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj] (d : ℕ)
    (hd : 1 ≤ d) (hpositive : 0 < Fintype.card W)
    (hden : d * Fintype.card W ≤ edgeCount H)
    (hminor : IsMinor H G)
    (hmin : ∀ {X : Type u} [Fintype X] (J : SimpleGraph X),
      IsMinor J G → 0 < Fintype.card X → d * Fintype.card X ≤ edgeCount J →
      Fintype.card W + edgeCount H ≤ Fintype.card X + edgeCount J) :
    ∀ v : W, 0 < H.degree v := by
  classical
  have hepos : 0 < edgeCount H := by
    have hmul : 0 < d * Fintype.card W := Nat.mul_pos (by omega) hpositive
    omega
  have hcard2 : 1 < Fintype.card W := by
    by_contra hcard
    have hlt : Fintype.card W < 2 := by omega
    have hmax : edgeCount H ≤ (Fintype.card W).choose 2 := by
      rw [edgeCount_eq_card_edgeFinset]
      exact H.card_edgeFinset_le_card_choose_two
    rw [Nat.choose_eq_zero_of_lt hlt] at hmax
    omega
  intro v
  by_contra hdegree
  have hvzero : H.degree v = 0 := by omega
  let J := H.induce (({v} : Set W)ᶜ)
  have hJcard : Fintype.card ↥(({v} : Set W)ᶜ) = Fintype.card W - 1 :=
    card_compl_singleton_eq_sub_one v
  have hJpos : 0 < Fintype.card ↥(({v} : Set W)ᶜ) := by omega
  have hJbalance : edgeCount J + H.degree v = edgeCount H :=
    edgeCount_induce_compl_singleton_add_degree H v
  have hJeq : edgeCount J = edgeCount H := by omega
  have hJminorH : IsMinor J H := induce_isMinor H _
  have hJminorG : IsMinor J G := IsMinor.trans hJminorH hminor
  have hJden : d * Fintype.card ↥(({v} : Set W)ᶜ) ≤ edgeCount J := by
    have hmul : d * Fintype.card ↥(({v} : Set W)ᶜ) ≤ d * Fintype.card W := by
      apply Nat.mul_le_mul_left
      omega
    omega
  have hcontradict := hmin J hJminorG hJpos hJden
  rw [hJcard, hJeq] at hcontradict
  omega

/-- In a graph with exactly `d` edges per vertex, some vertex has degree
at most `2d`.
@isnad1 id=ex.2h3v.s6.b7111fc378ef from=translated src=- shape=9d29a5d9 vocab=aa412d56
-/
theorem exists_degree_le_two_density (H : SimpleGraph V) [DecidableRel H.Adj]
    (d : ℕ) (hpositive : 0 < Fintype.card V)
    (hexact : edgeCount H = d * Fintype.card V) :
    ∃ v : V, H.degree v ≤ 2 * d := by
  classical
  haveI : Nonempty V := Fintype.card_pos_iff.mp hpositive
  have hsum : (∑ v : V, H.degree v) ≤ ∑ _v : V, 2 * d := by
    rw [sum_degree_eq_two_edgeCount H, hexact]
    simp
    nlinarith
  obtain ⟨v, _, hv⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨v, hv⟩

/-- A vertex's degree inside a neighborhood is the number of common
neighbors with its center.
@isnad1 id=eq.0h4v.s8.4cca309e7ec6 from=translated src=- shape=01d12fc0 vocab=3c1d3b67
-/
theorem degree_induce_neighborSet_eq_commonNeighbors
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (w : G.neighborSet v) :
    (G.induce (G.neighborSet v)).degree w =
      Fintype.card (G.commonNeighbors v w) := by
  classical
  let e : (G.induce (G.neighborSet v)).neighborSet w ≃
      G.commonNeighbors v w := {
    toFun := fun x => ⟨x.1.1, by
      rw [G.mem_commonNeighbors]
      exact ⟨x.1.property, x.property⟩⟩
    invFun := fun x => ⟨⟨x.1, (G.mem_commonNeighbors.mp x.property).1⟩,
      (G.mem_commonNeighbors.mp x.property).2⟩
    left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; rfl
    right_inv := by intro x; apply Subtype.ext; rfl
  }
  rw [← (G.induce (G.neighborSet v)).card_neighborSet_eq_degree]
  exact Fintype.card_congr e

/-- Contracting an edge lowers the vertex count by one.
@isnad1 id=eq.1h4v.s6.e55349f3e67e from=translated src=- shape=4ba181f0 vocab=69e18125
-/
theorem edgeContraction_card_add_one [DecidableEq V] (G : SimpleGraph V)
    {a b : V} (hab : G.Adj a b) :
    Fintype.card (EdgeContractionVertex a b) + 1 = Fintype.card V := by
  classical
  let S : Finset V := {a, b}ᶜ
  have hout : Fintype.card {x : V // x ≠ a ∧ x ≠ b} = S.card := by
    apply Fintype.card_of_subtype
    intro x
    simp [S]
  have hpair : ({a, b} : Finset V).card = 2 := Finset.card_pair hab.ne
  have htotal : S.card + 2 = Fintype.card V := by
    have h := Finset.card_compl_add_card ({a, b} : Finset V)
    simpa [S, hpair] using h
  change Fintype.card (Option {x : V // x ≠ a ∧ x ≠ b}) + 1 = Fintype.card V
  rw [Fintype.card_option, hout]
  omega

/-- Minimality under edge contraction forces at least `d` common neighbors
at every edge of an exact-density minor.
@isnad1 id=le.4h7v.s7.e68f066db3c6 from=translated src=- shape=b2c39f31 vocab=4aa965a7
-/
theorem common_neighbor_finset_card_ge_of_minimal_dense_minor
    {W : Type u} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj] (d : ℕ)
    (hminor : IsMinor H G)
    (hexact : edgeCount H = d * Fintype.card W)
    (hmin : ∀ {X : Type u} [Fintype X] (J : SimpleGraph X),
      IsMinor J G → 0 < Fintype.card X → d * Fintype.card X ≤ edgeCount J →
      Fintype.card W + edgeCount H ≤ Fintype.card X + edgeCount J) :
    ∀ ⦃a b : W⦄, H.Adj a b →
      d ≤ (H.neighborFinset a ∩ H.neighborFinset b).card := by
  classical
  intro a b hab
  let Q := edgeContraction H hab
  have hnH : 1 < Fintype.card W :=
    Fintype.one_lt_card_iff.mpr ⟨a, b, hab.ne⟩
  have hcard : Fintype.card (EdgeContractionVertex a b) + 1 = Fintype.card W :=
    edgeContraction_card_add_one H hab
  have hQpos : 0 < Fintype.card (EdgeContractionVertex a b) := by omega
  have hcount : edgeCount Q + 1 +
      (H.neighborFinset a ∩ H.neighborFinset b).card = edgeCount H :=
    edgeContraction_edgeCount_add_one_add_common hab
  by_contra hsmall
  have hc : (H.neighborFinset a ∩ H.neighborFinset b).card < d := by omega
  have hmul : d * Fintype.card W =
      d * Fintype.card (EdgeContractionVertex a b) + d := by
    rw [← hcard]
    ring
  have hQdense : d * Fintype.card (EdgeContractionVertex a b) ≤ edgeCount Q := by
    omega
  have hQminorG : IsMinor Q G :=
    IsMinor.trans (edgeContraction_isMinor H hab) hminor
  have hminimal := hmin Q hQminorG hQpos hQdense
  omega
/-- The dense-minor reduction in the form used by the clique-minor argument:
an exact-density minor has a vertex of degree at most `2d`, and every vertex
of its open neighborhood has at least `d` neighbors within that neighborhood.
@isnad1 id=ex.3h3v.s8.ad548493d946 from=translated src=- shape=38c6924c vocab=ad7c4946
-/
theorem exists_dense_neighborhood_minor
    (G : SimpleGraph V) (d : ℕ) (hd : 1 ≤ d)
    (hnonempty : 0 < Fintype.card V)
    (hdense : d * Fintype.card V ≤ edgeCount G) :
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W)
      (_ : DecidableEq W) (_ : DecidableRel H.Adj) (v : W),
      IsMinor H G ∧ edgeCount H = d * Fintype.card W ∧
      (∀ w : W, 0 < H.degree w) ∧ H.degree v ≤ 2 * d ∧
      (∀ w : H.neighborSet v,
        d ≤ (H.induce (H.neighborSet v)).degree w) := by
  classical
  obtain ⟨W, instW, H, hminor, hpositive, hexact, hmin⟩ :=
    exists_edge_exact_dense_minor G d hnonempty hdense
  letI : Fintype W := instW
  letI : DecidableEq W := Classical.decEq W
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  obtain ⟨v, hv⟩ := exists_degree_le_two_density H d hpositive hexact
  refine ⟨W, instW, H, inferInstance, inferInstance, v, hminor, hexact, ?_, hv, ?_⟩
  · exact no_isolated_of_minimal_dense_minor G H d hd hpositive
      (by omega) hminor hmin
  · intro w
    have hcommon := common_neighbor_finset_card_ge_of_minimal_dense_minor
      G H d hminor hexact hmin w.property
    have hcard : Fintype.card (H.commonNeighbors v w) =
        (H.neighborFinset v ∩ H.neighborFinset w).card := by
      apply Fintype.card_of_subtype
      intro x
      simp only [H.mem_commonNeighbors, Finset.mem_inter, H.mem_neighborFinset]
    rw [degree_induce_neighborSet_eq_commonNeighbors H v w, hcard]
    exact hcommon
/-- Summing a lower bound on every degree gives a lower bound on twice the
edge count.
@isnad1 id=le.1h3v.s6.02db1599b3ec from=translated src=- shape=cfbd88f1 vocab=42f21f6e
-/
theorem twice_edgeCount_ge_card_mul_min_degree
    (H : SimpleGraph V) [DecidableRel H.Adj] (d : ℕ)
    (hmin : ∀ v : V, d ≤ H.degree v) :
    d * Fintype.card V ≤ 2 * edgeCount H := by
  classical
  have hsum : (∑ _v : V, d) ≤ ∑ v : V, H.degree v := by
    apply Finset.sum_le_sum
    intro v _
    exact hmin v
  simpa [sum_degree_eq_two_edgeCount H, Nat.mul_comm] using hsum

/-- Minimum degree at least `2k` gives edge density at least `k`.
@isnad1 id=le.1h3v.s6.b861c11c7e74 from=translated src=- shape=c926d230 vocab=42f21f6e
-/
theorem edgeCount_ge_card_mul_of_min_degree_twice
    (H : SimpleGraph V) [DecidableRel H.Adj] (k : ℕ)
    (hmin : ∀ v : V, 2 * k ≤ H.degree v) :
    k * Fintype.card V ≤ edgeCount H := by
  have h := twice_edgeCount_ge_card_mul_min_degree H (2 * k) hmin
  nlinarith
/-- Convert a real edge-per-vertex bound to its integer edge-count form.
@isnad1 id=le.1h3v.s5.a4dbf31b83e4 from=translated src=- shape=6f36d37b vocab=dd801e06
-/
theorem edgeCount_ge_card_mul_of_edgeDensity_ge
    (G : SimpleGraph V) (d : ℕ)
    (hdense : (d : ℝ) ≤ edgeDensity G) :
    d * Fintype.card V ≤ edgeCount G := by
  by_cases hn : 0 < Fintype.card V
  · have hdenpos : (0 : ℝ) < (Fintype.card V : ℝ) := Nat.cast_pos.mpr hn
    have hreal : (d : ℝ) * (Fintype.card V : ℝ) ≤ (edgeCount G : ℝ) := by
      apply (le_div_iff₀ hdenpos).mp
      simpa [edgeDensity] using hdense
    exact_mod_cast hreal
  · have hzero : Fintype.card V = 0 := by omega
    simp [hzero]
/-- Deleting a finite vertex set lowers every remaining degree by at most
the number of deleted vertices.
@isnad1 id=le.1h4v.s8.e3cc73d307a9 from=translated src=- shape=c7b13c01 vocab=c9cc364b
-/
theorem degree_le_degree_induce_compl_add_card
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) [DecidableRel (G.induce (U : Set V)ᶜ).Adj]
    (v : V) (hv : v ∉ U) :
    G.degree v ≤
      (G.induce (U : Set V)ᶜ).degree ⟨v, hv⟩ + U.card := by
  classical
  let emb : ↥((U : Set V)ᶜ) ↪ V :=
    Function.Embedding.subtype (· ∈ (U : Set V)ᶜ)
  have hmap :
      ((G.induce (U : Set V)ᶜ).neighborFinset ⟨v, hv⟩).map emb =
        G.neighborFinset v ∩ Uᶜ := by
    ext x
    simp [emb]
  have hcard : (G.induce (U : Set V)ᶜ).degree ⟨v, hv⟩ =
      (G.neighborFinset v ∩ Uᶜ).card := by
    have hc := congrArg Finset.card hmap
    simp only [Finset.card_map] at hc
    rw [← (G.induce (U : Set V)ᶜ).card_neighborFinset_eq_degree]
    simpa using hc
  have hpartition := Finset.card_sdiff_add_card_inter (G.neighborFinset v) U
  have hinter : (G.neighborFinset v ∩ U).card ≤ U.card :=
    Finset.card_le_card Finset.inter_subset_right
  rw [← G.card_neighborFinset_eq_degree, hcard]
  have hsdiff : G.neighborFinset v ∩ Uᶜ = G.neighborFinset v \ U := by
    ext x
    simp
  rw [hsdiff]
  omega
end HadwigerLean
