/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Finite.Density
import Tengoku.RegularityLemmata.RegularityLemmata.Finite.Injective
import Tengoku.Seed.Combinatorics.SimpleGraph.Clique
import Tengoku.Seed.Combinatorics.Hypergraph.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Uniform hypergraphs

`UniformHypergraph r V`: a set of unordered `r`-element edges over `V`. The file
provides the complete and empty hypergraphs, edge density and restricted density
(both `0` on an empty denominator, per the library convention), the **ordered
injective-tuple realization** with its exact count

`tupleCount (realization) = r! · #edges`   (`orderedCount_eq`),

and the `r = 2` / `r = 3` adapters to `SimpleGraph` — including the ordered-triangle
conversion `= 6 · #cliqueFinset 3` deferred from the graph removal bridge.

Mathlib's `Hypergraph` (`Mathlib.Combinatorics.Hypergraph.Basic`, E. Spotte-Smith and
B. Mehta) is set-based (`Set α` vertices, `Set (Set α)` edges) and not uniformity- or
computation-oriented; this library needs a **finite, computable, arity-indexed**
representation so that counts are `ℕ`-valued and small instances close by `decide`,
hence the separate `UniformHypergraph` type. The `toHypergraph` bridge embeds it into
mathlib's notion.
-/

namespace RegularityLemmata

variable {V : Type*} {r : ℕ}

/-- An `r`-uniform hypergraph: a finite set of unordered `r`-element edges.-/
structure UniformHypergraph (r : ℕ) (V : Type*) where
  /-- The edge set.-/
  edges : Finset (Finset V)
  /-- Every edge has exactly `r` vertices.-/
  card_eq : ∀ e ∈ edges, e.card = r

namespace UniformHypergraph

/-- The complete `r`-uniform hypergraph on a finite vertex type.-/
def complete (r : ℕ) (V : Type*) [Fintype V] [DecidableEq V] : UniformHypergraph r V :=
  ⟨Finset.univ.powersetCard r, fun _ he => (Finset.mem_powersetCard.mp he).2⟩

/-- The empty `r`-uniform hypergraph.-/
def empty (r : ℕ) (V : Type*) : UniformHypergraph r V :=
  ⟨∅, fun _ he => absurd he (Finset.notMem_empty _)⟩

/-- The symmetric difference: edges on which two hypergraphs disagree.-/
def symmDiff [DecidableEq V] (H G : UniformHypergraph r V) : UniformHypergraph r V :=
  ⟨(H.edges \ G.edges) ∪ (G.edges \ H.edges), fun e he => by
    rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff] at he
    rcases he with ⟨he, -⟩ | ⟨he, -⟩
    · exact H.card_eq e he
    · exact G.card_eq e he⟩

/-- Membership in the symmetric difference, in the house `¬(↔)` form.
@isnad1 id=iff.0h5v.s6.5e8dfe40e491 from=translated src=- shape=33ca459b vocab=7fefe59d
-/
theorem mem_symmDiff [DecidableEq V] {H G : UniformHypergraph r V} {e : Finset V} :
    e ∈ (H.symmDiff G).edges ↔ ¬(e ∈ H.edges ↔ e ∈ G.edges) := by
  rw [symmDiff]
  simp only [Finset.mem_union, Finset.mem_sdiff]
  tauto

/-- Every edge set is contained in the complete one.
@isnad1 id=le.0h3v.s5.c7e3f9bdd2aa from=translated src=- shape=bc357481 vocab=32093452
-/
theorem edges_subset_powersetCard [Fintype V] [DecidableEq V] (H : UniformHypergraph r V) :
    H.edges ⊆ Finset.univ.powersetCard r := fun e he =>
  Finset.mem_powersetCard.mpr ⟨Finset.subset_univ e, H.card_eq e he⟩

/--
@isnad1 id=le.0h3v.s4.dfeecfceb584 from=translated src=- shape=3fb806dc vocab=be846d91
-/
theorem card_edges_le [Fintype V] [DecidableEq V] (H : UniformHypergraph r V) :
    H.edges.card ≤ (Fintype.card V).choose r := by
  refine le_trans (Finset.card_le_card H.edges_subset_powersetCard) (le_of_eq ?_)
  rw [Finset.card_powersetCard, Finset.card_univ]

/-! ### Densities -/

/-- Edge density: `#edges / C(|V|, r)`; `0` when `r > |V|` (zero denominator).-/
noncomputable def density [Fintype V] (H : UniformHypergraph r V) : ℝ :=
  (H.edges.card : ℝ) / ((Fintype.card V).choose r : ℝ)

/-- Density restricted to a vertex subset: edges inside `W` against `C(|W|, r)`.-/
noncomputable def restrictedDensity [DecidableEq V] (H : UniformHypergraph r V)
    (W : Finset V) : ℝ :=
  ((H.edges.filter (· ⊆ W)).card : ℝ) / ((W.card.choose r : ℕ) : ℝ)

/--
@isnad1 id=le.0h3v.s4.0916a176b0a2 from=translated src=- shape=4bf90389 vocab=42123bd0
-/
theorem density_nonneg [Fintype V] (H : UniformHypergraph r V) : 0 ≤ H.density := by
  unfold density
  positivity

/--
@isnad1 id=le.0h3v.s4.7115be281679 from=translated src=- shape=c9f20f02 vocab=a989b480
-/
theorem density_le_one [Fintype V] [DecidableEq V] (H : UniformHypergraph r V) :
    H.density ≤ 1 := by
  unfold density
  rcases Nat.eq_zero_or_pos ((Fintype.card V).choose r) with h0 | hpos
  · rw [h0]
    norm_num
  · rw [div_le_one (by exact_mod_cast hpos)]
    exact_mod_cast H.card_edges_le

/--
@isnad1 id=le.0h4v.s4.e7ce2fdd028e from=translated src=- shape=c0795de2 vocab=45b7ed9f
-/
theorem restrictedDensity_nonneg [DecidableEq V] (H : UniformHypergraph r V)
    (W : Finset V) : 0 ≤ H.restrictedDensity W := by
  unfold restrictedDensity
  positivity

/--
@isnad1 id=le.0h4v.s4.824262b6eba4 from=translated src=- shape=433b29ea vocab=45b7ed9f
-/
theorem restrictedDensity_le_one [DecidableEq V] (H : UniformHypergraph r V)
    (W : Finset V) : H.restrictedDensity W ≤ 1 := by
  unfold restrictedDensity
  rcases Nat.eq_zero_or_pos (W.card.choose r) with h0 | hpos
  · rw [h0]
    norm_num
  · rw [div_le_one (by exact_mod_cast hpos)]
    have hsub : H.edges.filter (· ⊆ W) ⊆ W.powersetCard r := by
      intro e he
      rw [Finset.mem_filter] at he
      exact Finset.mem_powersetCard.mpr ⟨he.2, H.card_eq e he.1⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_powersetCard] at this
    exact_mod_cast this

/-- The complete hypergraph has density `1` whenever the denominator is positive
(`r ≤ |V|`); the zero-denominator convention gives `0` otherwise.
@isnad1 id=eq.1h2v.s5.993b6bea8543 from=translated src=- shape=6b1a187d vocab=069e1ca3
-/
theorem density_complete [Fintype V] [DecidableEq V] (hr : r ≤ Fintype.card V) :
    (complete r V).density = 1 := by
  unfold density complete
  rw [show (Finset.univ.powersetCard r : Finset (Finset V)).card
      = (Fintype.card V).choose r from by rw [Finset.card_powersetCard, Finset.card_univ]]
  have hpos : 0 < (Fintype.card V).choose r := Nat.choose_pos hr
  rw [div_self]
  exact_mod_cast hpos.ne'

/--
@isnad1 id=eq.0h2v.s4.e5b2f6596346 from=translated src=- shape=854112cc vocab=71e676a2
-/
@[simp] theorem density_empty [Fintype V] : (empty r V).density = 0 := by
  unfold density empty
  simp

/-- Bridge to mathlib's set-based `Hypergraph`: full vertex set, edge finsets
coerced to sets.-/
def toHypergraph (H : UniformHypergraph r V) : Hypergraph V where
  vertexSet := Set.univ
  edgeSet := (fun e : Finset V => (e : Set V)) '' ↑H.edges
  subset_vertexSet_of_mem_edgeSet' := fun _ _ => Set.subset_univ _

/--
@isnad1 id=iff.0h4v.s5.c6249d88bf27 from=translated src=- shape=2e6b3a32 vocab=1fa5975a
-/
theorem coe_mem_toHypergraph_edgeSet {H : UniformHypergraph r V} {e : Finset V} :
    (e : Set V) ∈ H.toHypergraph.edgeSet ↔ e ∈ H.edges := by
  rw [toHypergraph]
  constructor
  · rintro ⟨e', he', heq⟩
    rwa [← Finset.coe_injective heq]
  · intro he
    exact ⟨e, he, rfl⟩

/-! ### The ordered injective-tuple realization -/

/-- The ordered realization: injective `r`-tuples whose underlying set is an edge.-/
def orderedRel [DecidableEq V] (H : UniformHypergraph r V) : (Fin r → V) → Prop :=
  fun v => Function.Injective v ∧ tupleRange v ∈ H.edges

instance [DecidableEq V] (H : UniformHypergraph r V) : DecidablePred H.orderedRel :=
  fun _ => instDecidableAnd

/-- Injective tuples with a prescribed `r`-element range number exactly `r!`.
@isnad1 id=eq.1h3v.s6.b571e3378a1c from=translated src=- shape=295f798f vocab=361cac1b
-/
theorem card_injective_tuples_range_eq [Fintype V] [DecidableEq V] {e : Finset V}
    (he : e.card = r) :
    ((Finset.univ : Finset (Fin r → V)).filter
      (fun v => Function.Injective v ∧ tupleRange v = e)).card = r.factorial := by
  classical
  have hcard : Fintype.card { x // x ∈ e } = r := by
    rw [Fintype.card_coe, he]
  rw [show r.factorial = injectiveTupleCount { x // x ∈ e } r from by
    rw [injectiveTupleCount_eq_descFactorial, hcard, Nat.descFactorial_self]]
  refine Finset.card_bij (fun v hv i => (⟨v i, by
    rw [Finset.mem_filter] at hv
    exact hv.2.2 ▸ Finset.mem_image_of_mem v (Finset.mem_univ i)⟩ : { x // x ∈ e }))
    ?_ ?_ ?_
  · intro v hv
    rw [Finset.mem_filter] at hv
    rw [mem_injectiveTuples]
    intro i j hij
    exact hv.2.1 (congrArg Subtype.val hij)
  · intro v hv v' hv' heq
    funext i
    exact congrArg Subtype.val (congrFun heq i)
  · intro w hw
    rw [mem_injectiveTuples] at hw
    refine ⟨fun i => (w i : V), ?_, ?_⟩
    · rw [Finset.mem_filter]
      have hinj : Function.Injective fun i => (w i : V) := fun i j hij =>
        hw (Subtype.ext hij)
      refine ⟨Finset.mem_univ _, hinj, ?_⟩
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro x hx
        rw [tupleRange, Finset.mem_image] at hx
        obtain ⟨i, _, rfl⟩ := hx
        exact (w i).2
      · rw [he, card_tupleRange_of_injective hinj]
    · funext i
      rfl

/-- **Ordered realization count.** The ordered injective tuples realizing a uniform
hypergraph number exactly `r! · #edges`.
@isnad1 id=eq.0h3v.s5.2b0557b034f9 from=translated src=- shape=7c188ad3 vocab=68edaf4d
-/
theorem orderedCount_eq [Fintype V] [DecidableEq V] (H : UniformHypergraph r V) :
    tupleCount H.orderedRel (fun _ => Finset.univ) = r.factorial * H.edges.card := by
  classical
  rw [tupleCount]
  have hbox : (Fintype.piFinset fun _ : Fin r => (Finset.univ : Finset V))
      = Finset.univ := by
    ext v
    simp
  rw [hbox]
  have hmap : ∀ v ∈ Finset.univ.filter H.orderedRel, tupleRange v ∈ H.edges := by
    intro v hv
    rw [Finset.mem_filter] at hv
    exact hv.2.2
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  have hfiber : ∀ e ∈ H.edges,
      ((Finset.univ.filter H.orderedRel).filter (fun v => tupleRange v = e)).card
        = r.factorial := by
    intro e he
    rw [Finset.filter_filter]
    have hcongr : Finset.univ.filter (fun v => H.orderedRel v ∧ tupleRange v = e)
        = Finset.univ.filter (fun v => Function.Injective v ∧ tupleRange v = e) := by
      refine Finset.filter_congr fun v _ => ?_
      rw [orderedRel]
      constructor
      · rintro ⟨⟨hinj, _⟩, hre⟩
        exact ⟨hinj, hre⟩
      · rintro ⟨hinj, hre⟩
        exact ⟨⟨hinj, hre ▸ he⟩, hre⟩
    rw [hcongr]
    exact card_injective_tuples_range_eq (H.card_eq e he)
  rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-! ### SimpleGraph adapters (`r = 2`, `r = 3`) -/

/-- The `2`-uniform hypergraph of a simple graph's edges (as `2`-cliques).-/
def ofSimpleGraph [DecidableEq V] [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    UniformHypergraph 2 V :=
  ⟨G.cliqueFinset 2, fun _ he => (SimpleGraph.mem_cliqueFinset_iff.mp he).2⟩

/-- Membership in the graph adapter is adjacency of an unordered pair.
@isnad1 id=iff.0h3v.s6.e5e85058d6d7 from=translated src=- shape=632ec522 vocab=5ca7794e
-/
theorem mem_ofSimpleGraph [DecidableEq V] [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {e : Finset V} :
    e ∈ (ofSimpleGraph G).edges ↔ ∃ a b, G.Adj a b ∧ e = {a, b} := by
  rw [ofSimpleGraph]
  simp only [SimpleGraph.mem_cliqueFinset_iff]
  constructor
  · intro h
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h.card_eq
    exact ⟨a, b, h.isClique (by simp) (by simp) hab, rfl⟩
  · rintro ⟨a, b, hab, rfl⟩
    refine ⟨?_, Finset.card_pair (G.ne_of_adj hab)⟩
    intro x hx y hy hxy
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
      Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact hab
    · exact hab.symm
    · exact absurd rfl hxy

/-- The `3`-uniform hypergraph of a graph's triangles.-/
def triangles [DecidableEq V] [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    UniformHypergraph 3 V :=
  ⟨G.cliqueFinset 3, fun _ he => (SimpleGraph.mem_cliqueFinset_iff.mp he).2⟩

/-- **Ordered triangle count** (the conversion deferred from the removal bridge):
injective ordered triangles number `6 · #cliqueFinset 3`.
@isnad1 id=eq.0h2v.s6.e21f6755d138 from=translated src=- shape=a02be4d5 vocab=3dff11d2
-/
theorem orderedCount_triangles [DecidableEq V] [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    tupleCount (triangles G).orderedRel (fun _ => Finset.univ)
      = 6 * (G.cliqueFinset 3).card := by
  rw [orderedCount_eq]
  rfl

end UniformHypergraph

/-! ### Tests and adversarial examples -/

open UniformHypergraph

-- Complete 2-uniform hypergraph on 3 vertices: 3 edges, density 1.

end RegularityLemmata
