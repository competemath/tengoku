/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
module

public import Tengoku.Seed.Combinatorics.SimpleGraph.LapMatrix

namespace LeanPoolFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Problem 6: Large epsilon-light vertex subsets -- Laplacian Basics

Basic definitions: edge Laplacian, graph Laplacian, induced Laplacian,
epsilon-lightness. Fundamental properties: PSD, symmetry, equivalence
with mathlib's `lapMatrix`.

## Main definitions

- `Problem6.graphLaplacian`: graph Laplacian as sum of edge Laplacians
- `Problem6.inducedLaplacian`: Laplacian of the induced subgraph on S
- `Problem6.inducedSubgraph`: the induced subgraph on S as a `SimpleGraph V`
- `Problem6.IsEpsLight`: epsilon-lightness predicate

## Main theorems

- `Problem6.graphLaplacian_eq_lapMatrix`: equivalence with mathlib
- `Problem6.graphLaplacian_posSemidef`: graph Laplacian is PSD
- `Problem6.graphLaplacian_isHermitian`: graph Laplacian is symmetric
- `Problem6.inducedLaplacian_eq_lapMatrix`: inducedLaplacian = (inducedSubgraph G S).lapMatrix ℝ
- `Problem6.lapMatrix_loewner_mono`: Loewner monotonicity for lapMatrix
-/

@[expose] public section

open Finset Matrix BigOperators

noncomputable section

namespace Problem6

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The Laplacian matrix of a simple graph, defined as ∑_{e ∈ E} L_e
    where each L_e is the edge Laplacian.
    We use the standard definition L_{ij} = deg(i) if i=j, -1 if i~j, 0 otherwise. -/
def graphLaplacian (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  Matrix.of fun i j =>
    if i = j then ((Finset.univ.filter (G.Adj i)).card : ℝ)
    else if G.Adj i j then -1
    else 0

/-- The Laplacian of the induced subgraph on S: restricting to edges within S. -/
def inducedLaplacian (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Matrix V V ℝ :=
  Matrix.of fun i j =>
    if i = j then ((Finset.univ.filter (fun k => i ∈ S ∧ k ∈ S ∧ G.Adj i k)).card : ℝ)
    else if G.Adj i j ∧ i ∈ S ∧ j ∈ S then -1
    else 0

/-- A set S is ε-light if εL - L_S is positive semidefinite. -/
def IsEpsLight (G : SimpleGraph V) [DecidableRel G.Adj] (ε : ℝ) (S : Finset V) : Prop :=
  (ε • graphLaplacian G - inducedLaplacian G S).PosSemidef

/-! ### The induced subgraph as a SimpleGraph V

Using Mathlib's `Subgraph.induce` and `Subgraph.spanningCoe` to construct the induced
subgraph on S as a `SimpleGraph V`, connecting to Mathlib's `lapMatrix` API. -/

/-- The induced subgraph of G on S, as a `SimpleGraph V`.
    Uses Mathlib's `Subgraph.induce` + `spanningCoe` to stay in `SimpleGraph V`. -/
noncomputable abbrev inducedSubgraph (G : SimpleGraph V) (S : Finset V) : SimpleGraph V :=
  ((⊤ : G.Subgraph).induce (↑S)).spanningCoe

instance inducedSubgraphDecidableRelAdj (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : DecidableRel (inducedSubgraph G S).Adj := by
  intro v w
  simp only [inducedSubgraph, SimpleGraph.Subgraph.spanningCoe_adj,
    SimpleGraph.Subgraph.induce_adj, SimpleGraph.Subgraph.top_adj, Finset.mem_coe]
  infer_instance

omit [Fintype V] [DecidableEq V] in
/-- Adjacency in the induced subgraph:
`(inducedSubgraph G S).Adj v w ↔ G.Adj v w ∧ v ∈ S ∧ w ∈ S`.
@isnad1 id=iff.0h5v.s5.4a14baeb6cfc from=translated src=- shape=796f07ae vocab=aecc0fcd
-/
lemma inducedSubgraph_adj (G : SimpleGraph V)
    (S : Finset V) (v w : V) :
    (inducedSubgraph G S).Adj v w ↔ G.Adj v w ∧ v ∈ S ∧ w ∈ S := by
  simp only [inducedSubgraph, SimpleGraph.Subgraph.spanningCoe_adj,
    SimpleGraph.Subgraph.induce_adj, SimpleGraph.Subgraph.top_adj, Finset.mem_coe]
  tauto

omit [Fintype V] [DecidableEq V] in
/-- The induced subgraph is a subgraph of G.
@isnad1 id=le.0h3v.s4.c45a4fefd0f7 from=translated src=- shape=9be8bb50 vocab=cc67fbf4
-/
lemma inducedSubgraph_le (G : SimpleGraph V)
    (S : Finset V) : inducedSubgraph G S ≤ G :=
  fun _ _ h => ((inducedSubgraph_adj G S _ _).mp h).1

omit [Fintype V] [DecidableEq V] in
/-- Monotonicity: S ⊆ T implies inducedSubgraph G S ≤ inducedSubgraph G T.
@isnad1 id=le.1h4v.s5.77cd1edbc2b1 from=translated src=- shape=99d95237 vocab=cc67fbf4
-/
lemma inducedSubgraph_mono (G : SimpleGraph V)
    {S T : Finset V} (hST : S ⊆ T) :
    inducedSubgraph G S ≤ inducedSubgraph G T := by
  intro v w h
  rw [inducedSubgraph_adj] at h ⊢
  exact ⟨h.1, hST h.2.1, hST h.2.2⟩

/-- Bridge: `inducedLaplacian G S = graphLaplacian (inducedSubgraph G S)`.
@isnad1 id=eq.0h3v.s5.7a6a978c5985 from=translated src=- shape=abd5bb05 vocab=14810774
-/
lemma inducedLaplacian_eq_graphLaplacian_inducedSubgraph
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    inducedLaplacian G S = graphLaplacian (inducedSubgraph G S) := by
  ext i j
  simp only [inducedLaplacian, graphLaplacian, Matrix.of_apply]
  by_cases hij : i = j
  · subst hij; simp only [↓reduceIte]; congr 1
  · simp only [hij, ↓reduceIte]
    have h_iff : (inducedSubgraph G S).Adj i j ↔ G.Adj i j ∧ i ∈ S ∧ j ∈ S :=
      inducedSubgraph_adj G S i j
    simp_all

/-- The graph Laplacian equals the Mathlib lapMatrix (degree minus adjacency).
@isnad1 id=eq.0h2v.s5.d2b3964f0420 from=translated src=- shape=f8bad52d vocab=b70932c0
-/
lemma graphLaplacian_eq_lapMatrix (G : SimpleGraph V) [DecidableRel G.Adj] :
    graphLaplacian G = G.lapMatrix ℝ := by
  ext i j
  simp only [graphLaplacian, Matrix.of_apply, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
             SimpleGraph.adjMatrix, Matrix.diagonal_apply, Matrix.sub_apply, Matrix.of_apply]
  split_ifs with h1 h2
  · -- i = j, G.Adj i j: impossible for simple graph
    subst h1; exact absurd h2 (SimpleGraph.irrefl G)
  · -- i = j, ¬G.Adj i j
    subst h1
    simp only [sub_zero]; norm_cast
    rw [← SimpleGraph.card_neighborFinset_eq_degree]; congr 1
    simp [SimpleGraph.neighborFinset_eq_filter]
  · -- i ≠ j, G.Adj i j
    norm_num
  · -- i ≠ j, ¬G.Adj i j
    norm_num

/-- Bridge: `inducedLaplacian G S = (inducedSubgraph G S).lapMatrix ℝ`.
@isnad1 id=eq.0h3v.s5.375c6c1b0180 from=translated src=- shape=39c05761 vocab=230f56ef
-/
lemma inducedLaplacian_eq_lapMatrix (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    inducedLaplacian G S = (inducedSubgraph G S).lapMatrix ℝ := by
  rw [inducedLaplacian_eq_graphLaplacian_inducedSubgraph, graphLaplacian_eq_lapMatrix]

/-- The graph Laplacian is positive semidefinite.
    xᵀLx = ∑_{u~v} (x_u - x_v)² ≥ 0.
@isnad1 id=possemid.0h2v.s4.0e31d38e02d7 from=translated src=- shape=816774ba vocab=fe9506d6
-/
lemma graphLaplacian_posSemidef (G : SimpleGraph V) [DecidableRel G.Adj] :
    (graphLaplacian G).PosSemidef := by
  rw [graphLaplacian_eq_lapMatrix]
  exact SimpleGraph.posSemidef_lapMatrix ℝ G

/-- The graph Laplacian is symmetric (L is Hermitian since G.Adj is symmetric).
@isnad1 id=ishermit.0h2v.s5.8d238c5711d1 from=translated src=- shape=f39ea0c3 vocab=bb2937ce
-/
lemma graphLaplacian_isHermitian (G : SimpleGraph V) [DecidableRel G.Adj] :
    (graphLaplacian G).IsHermitian := by
  ext i j
  simp only [graphLaplacian, Matrix.of_apply, star_trivial, Matrix.conjTranspose_apply]
  by_cases hij : i = j
  · subst hij; rfl
  · by_cases hadj : G.Adj i j
    · have : ¬(j = i) := fun h => hij (h.symm)
      simp [hij, this, hadj, G.adj_symm hadj]
    · have : ¬G.Adj j i := fun h => hadj (G.adj_symm h)
      by_cases hji : j = i
      · exact absurd hji.symm hij
      · simp [hij, hji, hadj, this]

/-! ### Loewner monotonicity for lapMatrix -/

/-- Loewner monotonicity for graph Laplacians: if H₁ ≤ H₂ (subgraph ordering),
    then `(H₂.lapMatrix ℝ - H₁.lapMatrix ℝ).PosSemidef`.
    Proof: the difference equals the lapMatrix of the edge-difference graph, which is PSD.
@isnad1 id=possemid.1h3v.s6.e32522bb1aa8 from=translated src=- shape=722c1c4a vocab=bfdff2c7
-/
lemma lapMatrix_loewner_mono {H₁ H₂ : SimpleGraph V}
    [DecidableRel H₁.Adj] [DecidableRel H₂.Adj]
    (h : H₁ ≤ H₂) :
    (H₂.lapMatrix ℝ - H₁.lapMatrix ℝ).PosSemidef := by
  let H' : SimpleGraph V :=
    { Adj := fun v w => H₂.Adj v w ∧ ¬ H₁.Adj v w
      symm.symm := fun v w ⟨h2, h1⟩ => ⟨H₂.adj_symm h2, fun hh => h1 (H₁.adj_symm hh)⟩
      loopless.irrefl := fun v ⟨h2, _⟩ => (SimpleGraph.irrefl H₂) h2 }
  have : DecidableRel H'.Adj := inferInstance
  suffices heq : H₂.lapMatrix ℝ - H₁.lapMatrix ℝ = H'.lapMatrix ℝ by
    rw [heq]; exact SimpleGraph.posSemidef_lapMatrix ℝ H'
  -- Reduce to entry-wise matching via graphLaplacian formula
  have hGL : ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.lapMatrix ℝ =
      graphLaplacian G := fun G _ => (graphLaplacian_eq_lapMatrix G).symm
  rw [hGL, hGL, hGL]
  ext i j
  simp only [Matrix.sub_apply, graphLaplacian, Matrix.of_apply, H']
  by_cases hij : i = j
  · subst hij; simp only [↓reduceIte]
    have h_disj : Disjoint (univ.filter (H₁.Adj i))
        (univ.filter (fun k => H₂.Adj i k ∧ ¬H₁.Adj i k)) := by
      simp only [Finset.disjoint_filter]
      intro k _ h1 ⟨_, hn⟩; exact hn h1
    have h_union : univ.filter (H₂.Adj i) =
        univ.filter (H₁.Adj i) ∪ univ.filter (fun k => H₂.Adj i k ∧ ¬H₁.Adj i k) := by
      ext k; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
      constructor
      · intro h2; by_cases h1 : H₁.Adj i k
        · exact Or.inl h1
        · exact Or.inr ⟨h2, h1⟩
      · rintro (h1 | ⟨h2, _⟩)
        · exact h h1
        · exact h2
    simp_all
  · simp only [hij, ↓reduceIte]
    by_cases h2 : H₂.Adj i j
    · by_cases h1 : H₁.Adj i j
      · simp [h2, h1]
      · simp [h2, h1]
    · have h1 : ¬H₁.Adj i j := fun hh => h2 (h hh)
      simp [h2, h1]

end Problem6

end
