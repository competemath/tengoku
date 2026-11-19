import Tengoku.Linearhadwiger.HadwigerLean.Graph.Contraction
import Tengoku.Linearhadwiger.HadwigerLean.Graph.DensityBasic
import Tengoku.Linearhadwiger.HadwigerLean.Probability.FiniteSampling
import Tengoku.Linearhadwiger.HadwigerLean.Graph.DensityConnectivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Edges of a single-edge contraction

The contracted vertex is adjacent to exactly the union of the two original
neighborhoods outside the contracted pair. Edges among all other vertices are
unchanged. These formulas underlie the exact edge-count identity used in the
clique-density reduction.
-/

namespace HadwigerLean

universe u

variable {V : Type u} {G : SimpleGraph V} {a b : V}
  (hab : G.Adj a b)

/--
@isnad1 id=iff.1h5v.s6.329d9806cb78 from=translated src=- shape=ab04df16 vocab=d0083022
-/
theorem edgeContraction_adj_none_some
    (x : {v : V // v ≠ a ∧ v ≠ b}) :
    (edgeContraction G hab).Adj none (some x) ↔
      G.Adj a x ∨ G.Adj b x := by
  simp [edgeContraction, edgeContractionPartition,
    ConnectedPartition.touchingQuotient, edgeContractionBlock]

/--
@isnad1 id=iff.1h6v.s6.64571fb8b437 from=translated src=- shape=990eb34f vocab=c37f637d
-/
theorem edgeContraction_adj_some_some
    (x y : {v : V // v ≠ a ∧ v ≠ b}) :
    (edgeContraction G hab).Adj (some x) (some y) ↔ G.Adj x y := by
  simp [edgeContraction, edgeContractionPartition,
    ConnectedPartition.touchingQuotient, edgeContractionBlock]
  intro h hxy
  exact h.ne (congrArg Subtype.val hxy)

end HadwigerLean

namespace HadwigerLean

universe u

variable {V : Type u} {G : SimpleGraph V} {a b : V}

/-- The vertices surviving a contraction of a and b.-/
abbrev EdgeOutside (a b : V) := {v : V // v ≠ a ∧ v ≠ b}

/-- The noncontracted vertices of the quotient, viewed as an ordinary
subtype.-/
noncomputable def edgeOutsideEquiv :
    EdgeOutside a b ≃
      {q : EdgeContractionVertex a b // q ∈ ({none} : Set (EdgeContractionVertex a b))ᶜ} where
  toFun x := ⟨some x, by simp⟩
  invFun q := by
    cases h : q.1 with
    | none => exact False.elim (q.2 (by simpa [h]))
    | some x => exact x
  left_inv := by
    intro x
    rfl
  right_inv := by
    rintro ⟨q, hq⟩
    cases q with
    | none => exact False.elim (hq (by simp))
    | some x => rfl

/-- Away from its new vertex, a single-edge contraction is isomorphic to
the original graph induced on the surviving vertices.-/
noncomputable def edgeContractionOutsideIso (hab : G.Adj a b) :
    (G.induce {v : V | v ≠ a ∧ v ≠ b}) ≃g
      ((edgeContraction G hab).induce
        ({none} : Set (EdgeContractionVertex a b))ᶜ) where
  toEquiv := edgeOutsideEquiv (a := a) (b := b)
  map_rel_iff' := by
    intro x y
    change (edgeContraction G hab).Adj (some x) (some y) ↔ G.Adj x y
    exact edgeContraction_adj_some_some (G := G) hab x y

/-- Edge count is invariant under graph isomorphism.
@isnad1 id=eq.0h5v.s4.498ac84a2ab4 from=translated src=- shape=2a63277f vocab=5804e6c5
-/
theorem edgeCount_eq_of_iso {W : Type*} [Fintype V] [Fintype W]
    {H : SimpleGraph W} (e : G ≃g H) :
    edgeCount G = edgeCount H := by
  classical
  rw [edgeCount_eq_card_edgeFinset, edgeCount_eq_card_edgeFinset]
  exact e.card_edgeFinset_eq

end HadwigerLean

namespace HadwigerLean

universe u

variable {V : Type u} [Fintype V] {G : SimpleGraph V} {a b : V}

/-- The new vertex has one neighbor for each surviving vertex adjacent to
at least one end of the contracted edge.
@isnad1 id=eq.1h4v.s8.3a60fc639581 from=translated src=- shape=6cd4833b vocab=107735c1
-/
theorem edgeContraction_degree_none (hab : G.Adj a b)
    [DecidableEq V] [DecidableRel G.Adj]
    [DecidableRel (edgeContraction G hab).Adj] :
    (edgeContraction G hab).degree none =
      ((Finset.univ : Finset (EdgeOutside a b)).filter
        (fun x : EdgeOutside a b => G.Adj a x ∨ G.Adj b x)).card := by
  classical
  let Q := edgeContraction G hab
  let S : Finset (EdgeOutside a b) :=
    Finset.univ.filter (fun x : EdgeOutside a b => G.Adj a x ∨ G.Adj b x)
  have hneighbors :
      Q.neighborFinset none = S.image some := by
    ext q
    cases q with
    | none => simp [Q]
    | some x =>
        simp [S, Q, edgeContraction_adj_none_some (G := G) hab x]
  rw [← Q.card_neighborFinset_eq_degree none, hneighbors]
  exact Finset.card_image_of_injective S (Option.some_injective _)

end HadwigerLean

namespace HadwigerLean

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}

/-- The outside vertices adjacent to at least one contracted endpoint are
exactly the union of the two neighborhoods with the endpoints removed.
@isnad1 id=eq.0h4v.s8.32f06d8aaa82 from=translated src=- shape=e6266692 vocab=dd6312d9
-/
theorem edgeOutside_neighbor_filter_card :
    ((Finset.univ : Finset (EdgeOutside a b)).filter
      (fun x : EdgeOutside a b => G.Adj a x ∨ G.Adj b x)).card =
      ((G.neighborFinset a ∪ G.neighborFinset b) \ {a, b}).card := by
  classical
  let S : Finset (EdgeOutside a b) :=
    Finset.univ.filter (fun x : EdgeOutside a b => G.Adj a x ∨ G.Adj b x)
  let T : Finset V := (G.neighborFinset a ∪ G.neighborFinset b) \ {a, b}
  have himage : S.image Subtype.val = T := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, S, T]
    constructor
    · rintro ⟨y, hAdj, rfl⟩
      refine ⟨?_, ?_⟩
      · simpa only [SimpleGraph.mem_neighborFinset] using hAdj
      · simp [y.property.1, y.property.2]
    · rintro ⟨hAdj, hnot⟩
      have hx : x ≠ a ∧ x ≠ b := by
        simpa using hnot
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      simpa only [SimpleGraph.mem_neighborFinset] using hAdj
  change S.card = T.card
  rw [← himage]
  exact (Finset.card_image_of_injective S Subtype.val_injective).symm

end HadwigerLean

namespace HadwigerLean

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}

/-- The union of the two original neighborhoods includes both ends of the
contracted edge, while the new vertex sees exactly the other members.
@isnad1 id=eq.1h4v.s8.d587e41b1fb7 from=translated src=- shape=cb39dcc8 vocab=afed4e91
-/
theorem edgeContraction_degree_none_add_two (hab : G.Adj a b)
    [DecidableRel (edgeContraction G hab).Adj] :
    (edgeContraction G hab).degree none + 2 =
      (G.neighborFinset a ∪ G.neighborFinset b).card := by
  classical
  let N : Finset V := G.neighborFinset a ∪ G.neighborFinset b
  have ha : a ∈ N := by
    simp [N, hab.symm]
  have hb : b ∈ N := by
    simp [N, hab]
  have hsubset : ({a, b} : Finset V) ⊆ N := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  have hpair : ({a, b} : Finset V).card = 2 := by
    simp [hab.ne]
  have hsdiff := Finset.card_sdiff_add_card_eq_card hsubset
  rw [hpair] at hsdiff
  rw [edgeContraction_degree_none (G := G) hab,
    edgeOutside_neighbor_filter_card (G := G) (a := a) (b := b)]
  exact hsdiff

end HadwigerLean

namespace HadwigerLean

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}

/-- Edges touching either endpoint are the union of their incidence sets.
@isnad1 id=eq.0h4v.s6.50470d7d74f5 from=translated src=- shape=e7f292d5 vocab=5818b7da
-/
theorem edgeIncidenceCount_pair_eq_card_union :
    edgeIncidenceCount G {a, b} =
      (G.incidenceFinset a ∪ G.incidenceFinset b).card := by
  classical
  unfold edgeIncidenceCount
  congr 1
  ext e
  simp [G.incidenceFinset_eq_filter, Finset.mem_insert]
  tauto

/-- An edge at a and b is counted twice in the sum of their degrees, so
the number of edges touching the pair is one less.
@isnad1 id=eq.1h4v.s6.58a4598c9746 from=translated src=- shape=faf26ebb vocab=4dc95d34
-/
theorem edgeIncidenceCount_pair_add_one (hab : G.Adj a b) :
    edgeIncidenceCount G {a, b} + 1 = G.degree a + G.degree b := by
  classical
  have hinter :
      G.incidenceFinset a ∩ G.incidenceFinset b = {s(a, b)} := by
    ext e
    simp only [Finset.mem_inter, G.mem_incidenceFinset]
    rw [← Set.mem_inter_iff, G.incidenceSet_inter_incidenceSet_of_adj hab]
    simp
  have hcard : (G.incidenceFinset a ∩ G.incidenceFinset b).card = 1 := by
    rw [hinter]
    simp
  have hsum := Finset.card_union_add_card_inter
    (G.incidenceFinset a) (G.incidenceFinset b)
  rw [hcard, G.card_incidenceFinset_eq_degree,
    G.card_incidenceFinset_eq_degree] at hsum
  rw [edgeIncidenceCount_pair_eq_card_union]
  exact hsum

end HadwigerLean

namespace HadwigerLean

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}

/-- Every edge is either internal to the complement of S or touches S,
and these two classes partition the edge set.
@isnad1 id=eq.0h3v.s6.c657f099d882 from=translated src=- shape=e1ecc22d vocab=07b699fc
-/
theorem edgeCount_induce_compl_add_incidence (S : Finset V) :
    edgeCount (G.induce ((Sᶜ : Finset V) : Set V)) +
      edgeIncidenceCount G S = edgeCount G := by
  classical
  have hfilter :
      G.edgeFinset.filter (fun e => e.toFinset ⊆ Sᶜ) =
        G.edgeFinset.filter (fun e => ¬ ∃ v ∈ S, v ∈ e) := by
    ext e
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨he, hs⟩
      refine ⟨he, ?_⟩
      rintro ⟨v, hvS, hve⟩
      exact (Finset.mem_compl.mp (hs (Sym2.mem_toFinset.mpr hve))) hvS
    · rintro ⟨he, hn⟩
      refine ⟨he, ?_⟩
      intro v hv
      apply Finset.mem_compl.mpr
      intro hvS
      exact hn ⟨v, hvS, Sym2.mem_toFinset.mp hv⟩
  rw [← FiniteSampling.sampled_edges_eq_induced_count G Sᶜ]
  rw [hfilter]
  have hinc : edgeIncidenceCount G S =
      (G.edgeFinset.filter (fun e => ∃ v ∈ S, v ∈ e)).card := by
    unfold edgeIncidenceCount
    congr 1
    ext e
    simp
  rw [hinc, edgeCount_eq_card_edgeFinset]
  simpa only [add_comm] using
    (G.edgeFinset.card_filter_add_card_filter_not
      (fun e => ∃ v ∈ S, v ∈ e))

end HadwigerLean

namespace HadwigerLean

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}

/-- Exact simple-edge-contraction count: one contracted edge disappears,
and every common neighbor merges one further pair of edges.
@isnad1 id=eq.1h4v.s6.95544cd441f6 from=translated src=- shape=e55c7c25 vocab=827bcad4
-/
theorem edgeContraction_edgeCount_add_one_add_common
    (hab : G.Adj a b) :
    edgeCount (edgeContraction G hab) + 1 +
      (G.neighborFinset a ∩ G.neighborFinset b).card =
        edgeCount G := by
  classical
  let Q := edgeContraction G hab
  let O : Set V := {v | v ≠ a ∧ v ≠ b}
  have hset : (({a, b}ᶜ : Finset V) : Set V) = O := by
    ext v
    simp [O]
    tauto
  have horiginal := edgeCount_induce_compl_add_incidence
    (G := G) ({a, b} : Finset V)
  rw [hset] at horiginal
  have hquotient :
      edgeCount (Q.induce ({none} : Set (EdgeContractionVertex a b))ᶜ) +
        Q.degree none = edgeCount Q :=
    edgeCount_induce_compl_singleton_add_degree Q none
  have hiso :
      edgeCount (G.induce O) =
        edgeCount (Q.induce ({none} : Set (EdgeContractionVertex a b))ᶜ) := by
    exact edgeCount_eq_of_iso (edgeContractionOutsideIso hab)
  have hinc :
      edgeIncidenceCount G {a, b} + 1 =
        G.degree a + G.degree b :=
    edgeIncidenceCount_pair_add_one hab
  have hnew :
      Q.degree none + 2 =
        (G.neighborFinset a ∪ G.neighborFinset b).card :=
    edgeContraction_degree_none_add_two hab
  have hcard :=
    Finset.card_union_add_card_inter (G.neighborFinset a) (G.neighborFinset b)
  rw [G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at hcard
  change edgeCount Q + 1 + (G.neighborFinset a ∩ G.neighborFinset b).card =
    edgeCount G
  omega

end HadwigerLean
