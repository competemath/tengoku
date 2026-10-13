/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku

/-!
# Finite multigraphs, prefix cuts, and the graph-ordering hypothesis

A `Multigraph V E` records the two endpoints of every edge in `E`. Parallel
edges are distinct elements of `E` and are counted separately. For a vertex
ordering, the *cut after* a vertex is the set of edges with exactly one
endpoint among the vertices up to it; these are exactly the cuts of the lower
sets of the order.

`OrderingBound A η C` is the graph-ordering hypothesis with coefficient `A`:
every connected loopless multigraph of maximum degree three has a vertex
ordering whose prefix cuts have at most `(A + η) (M - N)⁺ + 3 log₂ N + C`
edges, where `N` and `M` are the numbers of vertices and edges. The circuit
lower bound takes this statement as a hypothesis and yields the coefficient
`1 + 1/A`. `Expansion` proves it for `A = 2 p` from a cubic pathwidth bound
with coefficient `p`, and for `A = 2 c` from a cubic cutwidth bound with
coefficient `c`; the Monien–Preis and Fomin–Høie bounds give `A = 1/3`.
-/

@[expose] public section

namespace Algebraic
namespace Cutwidth

open scoped Classical

/-- A multigraph: every edge has a first and a second endpoint. Parallel edges
are distinct elements of `E`. -/
structure Multigraph (V E : Type) where
  /-- The first endpoint of an edge. -/
  fst : E → V
  /-- The second endpoint of an edge. -/
  snd : E → V

namespace Multigraph

variable {V E : Type} (G : Multigraph V E)

/-- An edge is incident to each of its endpoints. -/
def Incident (v : V) (e : E) : Prop :=
  G.fst e = v ∨ G.snd e = v

/-- No edge joins a vertex to itself. -/
def Loopless : Prop :=
  ∀ e, G.fst e ≠ G.snd e

/-- Two vertices are adjacent when some edge joins them, in either direction. -/
def Adj (u v : V) : Prop :=
  ∃ e, (G.fst e = u ∧ G.snd e = v) ∨ (G.fst e = v ∧ G.snd e = u)

/--
@isnad1 id=adj.1h5v.s4.dedc12388976 from=translated src=- shape=16f4ca43 vocab=2dd3164e
-/
theorem Adj.symm {G : Multigraph V E} {u v : V} (h : G.Adj u v) : G.Adj v u := by
  obtain ⟨e, h | h⟩ := h
  · exact ⟨e, Or.inr h⟩
  · exact ⟨e, Or.inl h⟩

/-- Every two vertices are joined by a walk. -/
def Connected : Prop :=
  ∀ u v, Relation.ReflTransGen G.Adj u v

/-- Reachability along walks is symmetric.
@isnad1 id=refltran.1h5v.s4.faf8c03e0198 from=translated src=- shape=d22a52d8 vocab=7c7e8519
-/
theorem reflTransGen_adj_symm {G : Multigraph V E} {u v : V}
    (h : Relation.ReflTransGen G.Adj u v) : Relation.ReflTransGen G.Adj v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.head step.symm ih

/-- A multigraph in which every vertex reaches a common vertex is connected.
@isnad1 id=connecte.1h4v.s4.180b328ce7d6 from=translated src=- shape=472bf95f vocab=7cf0f5c1
-/
theorem connected_of_forall_reflTransGen {G : Multigraph V E} (root : V)
    (h : ∀ v, Relation.ReflTransGen G.Adj v root) : G.Connected :=
  fun u v => (h u).trans (reflTransGen_adj_symm (h v))

section Finite

variable [Fintype E]

/-- The edges incident to a vertex. -/
noncomputable def edgesAt (v : V) : Finset E :=
  Finset.univ.filter fun e => G.Incident v e

/--
@isnad1 id=iff.0h5v.s5.cfcdc81d2378 from=translated src=- shape=65e9cb56 vocab=3c46bc1a
-/
theorem mem_edgesAt {v : V} {e : E} : e ∈ G.edgesAt v ↔ G.Incident v e := by
  simp [edgesAt]

/-- The number of edges incident to a vertex. -/
noncomputable def degree (v : V) : Nat :=
  (G.edgesAt v).card

/-- Every vertex has at most `d` incident edges. -/
def MaxDegreeLE (d : Nat) : Prop :=
  ∀ v, G.degree v ≤ d

/-- The edges with exactly one endpoint in `L`. -/
noncomputable def cut (L : Finset V) : Finset E :=
  Finset.univ.filter fun e => ¬ (G.fst e ∈ L ↔ G.snd e ∈ L)

/--
@isnad1 id=iff.0h5v.s6.e1862d7167f9 from=translated src=- shape=cdbb3d64 vocab=82bfac22
-/
theorem mem_cut {L : Finset V} {e : E} :
    e ∈ G.cut L ↔ ¬ (G.fst e ∈ L ↔ G.snd e ∈ L) := by
  simp [cut]

/--
@isnad1 id=eq.0h3v.s4.272561b1d65a from=translated src=- shape=5e33f431 vocab=1c803068
-/
@[simp] theorem cut_empty : G.cut ∅ = ∅ := by
  ext e
  simp [mem_cut]

/--
@isnad1 id=eq.0h3v.s4.a75c8c8d1b34 from=translated src=- shape=57d6d156 vocab=f872127f
-/
@[simp] theorem cut_univ [Fintype V] : G.cut Finset.univ = ∅ := by
  ext e
  simp [mem_cut]

/-- An edge in a cut is incident to a vertex in the set and to one outside it.
@isnad1 id=or.1h5v.s6.54959c3b1c69 from=translated src=- shape=7de7c393 vocab=82bfac22
-/
theorem exists_mem_of_mem_cut {L : Finset V} {e : E} (h : e ∈ G.cut L) :
    (G.fst e ∈ L ∧ G.snd e ∉ L) ∨ (G.fst e ∉ L ∧ G.snd e ∈ L) := by
  rw [mem_cut] at h
  by_cases h₁ : G.fst e ∈ L <;> by_cases h₂ : G.snd e ∈ L <;> simp_all

/-- Every cut has at most `w` edges. -/
def CutsAtMost (L : Set (Finset V)) (w : Nat) : Prop :=
  ∀ S ∈ L, (G.cut S).card ≤ w

end Finite

/-- The graph-ordering hypothesis with coefficient `A`, slack `η`, and
additive constant `C`: every connected loopless multigraph of maximum degree
three has a linear vertex ordering all of whose lower-set cuts have at most
`(A + η) (M - N)⁺ + 3 log₂ N + C` edges, where `N` and `M` are the numbers
of vertices and edges. -/
def OrderingBound (A η C : ℝ) : Prop :=
  ∀ (V E : Type) [Fintype V] [Fintype E] (G : Multigraph V E),
    G.Loopless → G.MaxDegreeLE 3 → G.Connected →
    ∃ _ : LinearOrder V, ∀ L : Finset V, IsLowerSet (L : Set V) →
      ((G.cut L).card : ℝ) ≤
        (A + η) * max ((Fintype.card E : ℝ) - Fintype.card V) 0 +
          3 * Real.logb 2 (Fintype.card V) + C

end Multigraph

end Cutwidth
end Algebraic
