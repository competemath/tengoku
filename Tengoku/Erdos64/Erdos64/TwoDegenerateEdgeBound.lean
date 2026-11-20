import Tengoku.Erdos64.Erdos64.RootedBranches
import Tengoku.Seed.Combinatorics.SimpleGraph.DeleteEdges

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Internal degree is unchanged when a finite carrier in an induced graph is
viewed as a finite carrier in the ambient graph.-/
theorem internalDegree_induce_map
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [DecidablePred (· ∈ s)]
    (S : Finset s) (v : s) :
    internalDegree (G.induce s) S v =
      internalDegree G (S.map (.subtype (· ∈ s))) v.1 := by
  classical
  simp only [internalDegree, Finset.filter_map, Finset.card_map]
  rfl

private theorem two_degenerate_edge_bound_aux (n : ℕ) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = n →
      (∀ S : Finset V, S.Nonempty → ∃ v ∈ S, internalDegree G S v ≤ 2) →
      2 ≤ n → G.edgeFinset.card + 3 ≤ 2 * n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ G _ hcard hlow hn
    classical
    by_cases htwo : n = 2
    · have hedge := G.card_edgeFinset_le_card_choose_two
      rw [hcard, htwo] at hedge
      simp only [Nat.choose_self] at hedge
      omega
    have hnonempty : (Finset.univ : Finset V).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro he
      have := congrArg Finset.card he
      simp only [Finset.card_univ, Finset.card_empty] at this
      omega
    obtain ⟨v, _, hv⟩ := hlow Finset.univ hnonempty
    have hvdegree : G.degree v ≤ 2 := by
      simpa [internalDegree, ← SimpleGraph.neighborFinset_eq_filter] using hv
    let W := ({v}ᶜ : Set V)
    let H : SimpleGraph W := G.induce ({v}ᶜ : Set V)
    have hWcard : Fintype.card W = n - 1 := by
      change Fintype.card {w : V // ¬ w = v} = n - 1
      rw [Fintype.card_subtype_compl]
      simp [hcard]
    have hlowH : ∀ S : Finset W, S.Nonempty →
        ∃ w ∈ S, internalDegree H S w ≤ 2 := by
      intro S hS
      let emb : W ↪ V := .subtype (· ∈ ({v}ᶜ : Set V))
      obtain ⟨w, hw, hwdegree⟩ := hlow (S.map emb) hS.map
      obtain ⟨w, hwS, rfl⟩ := Finset.mem_map.mp hw
      refine ⟨w, hwS, ?_⟩
      change ((S.map emb).filter (G.Adj w.1)).card ≤ 2 at hwdegree
      rw [Finset.filter_map, Finset.card_map] at hwdegree
      exact hwdegree
    have hbound := ih (n - 1) (by omega) H hWcard hlowH (by omega)
    have hdelete : H.edgeFinset.card = G.edgeFinset.card - G.degree v := by
      exact (G.card_edgeFinset_induce_compl_singleton v).trans
        (G.card_edgeFinset_deleteIncidenceSet v)
    rw [hdelete] at hbound
    have hvle := G.degree_le_card_edgeFinset v
    omega

/-- A finite graph with a vertex of internal degree at most two in every
nonempty induced carrier has at most `2n - 3` edges when `n ≥ 2`.-/
theorem two_degenerate_edge_bound
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hlow : ∀ S : Finset V, S.Nonempty →
      ∃ v ∈ S, internalDegree G S v ≤ 2)
    (hn : 2 ≤ Fintype.card V) :
    G.edgeFinset.card + 3 ≤ 2 * Fintype.card V :=
  two_degenerate_edge_bound_aux (Fintype.card V) G rfl hlow hn

/-- Carrier form of the sharp two-degenerate edge bound.  The low-degree
hypothesis is required only for nonempty subcarriers of `S`.-/
theorem two_degenerate_induce_edge_bound
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V)
    (hlow : ∀ T : Finset V, T ⊆ S → T.Nonempty →
      ∃ v ∈ T, internalDegree G T v ≤ 2)
    (hn : 2 ≤ S.card) :
    (G.induce (↑S : Set V)).edgeFinset.card + 3 ≤ 2 * S.card := by
  classical
  have hlowS : ∀ T : Finset (↑S : Set V), T.Nonempty →
      ∃ v ∈ T, internalDegree (G.induce (↑S : Set V)) T v ≤ 2 := by
    intro T hT
    let emb : (↑S : Set V) ↪ V := .subtype (· ∈ (↑S : Set V))
    have hsub : T.map emb ⊆ S := by
      intro v hv
      obtain ⟨w, _, rfl⟩ := Finset.mem_map.mp hv
      exact w.2
    obtain ⟨v, hv, hvdegree⟩ := hlow (T.map emb) hsub hT.map
    obtain ⟨v, hvT, rfl⟩ := Finset.mem_map.mp hv
    refine ⟨v, hvT, ?_⟩
    change ((T.map emb).filter (G.Adj v.1)).card ≤ 2 at hvdegree
    rw [Finset.filter_map, Finset.card_map] at hvdegree
    exact hvdegree
  simpa using two_degenerate_edge_bound (G.induce (↑S : Set V)) hlowS
    (by simpa using hn)

end Erdos64
