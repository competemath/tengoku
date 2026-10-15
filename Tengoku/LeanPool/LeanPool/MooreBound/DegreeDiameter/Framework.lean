/-
Copyright (c) 2026 Wouter Cames van Batenburg, Samuel Korsky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Cames van Batenburg, Samuel Korsky
-/

module

public import Tengoku

/-!
# Generic finite-graph framework for the degree--diameter preprint

This file contains only generic graph definitions and lemmas.  In particular, it does not assume
the flag-graph construction or any asymptotic input.

We use `SimpleGraph.ediam`, not `SimpleGraph.diam`: the latter is defined to be zero when the
extended diameter is infinite, and would therefore allow disconnected graphs accidentally.

Lean Pool port of wewantmoore commit d59bd80ea93fabb9faf769e790ab47692645e022.
The port adds a namespace and adapts proofs to the current Mathlib APIs and repository style.
-/

@[expose] public section

namespace MooreBound

open Set

namespace DegreeDiameter

open SimpleGraph

universe u

/-- Every vertex of `G` has degree at most `d`, expressed without choosing a decidable adjacency
relation.  For a finite vertex type, `Set.ncard (G.neighborSet v)` is the ordinary vertex degree. -/
noncomputable def MaxDegreeLE {V : Type*} (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ v, (G.neighborSet v).ncard ≤ d

/-! ## A coarse breadth-first bound -/

/-- One legal breadth-first move: stay at the current vertex, or cross one edge. -/
def ClosedNeighbor {V : Type u} (G : SimpleGraph V) (x : V) :=
  {y : V // x = y ∨ G.Adj x y}

/--
@isnad1 id=finite.0h3v.s3.341a750fdbd7 from=translated src=- shape=3f15ade1 vocab=454d6013
-/
instance finite_closedNeighbor {V : Type u} [Finite V] (G : SimpleGraph V) (x : V) :
    Finite (ClosedNeighbor G x) :=
  Finite.of_injective Subtype.val Subtype.val_injective

/--
@isnad1 id=eq.0h3v.s5.eebd4fc465f0 from=translated src=- shape=e31acc52 vocab=46b4ce2e
-/
lemma setOf_closedNeighbor_eq_insert {V : Type u} (G : SimpleGraph V) (x : V) :
    {y : V | x = y ∨ G.Adj x y} = insert x (G.neighborSet x) := by
  ext y
  simp [eq_comm]

/--
@isnad1 id=le.1h4v.s5.7a89c812a54e from=translated src=- shape=06b8eb5a vocab=003dd44c
-/
lemma natCard_closedNeighbor_le {V : Type u} [Finite V] {G : SimpleGraph V} {d : ℕ}
    (hdegree : MaxDegreeLE G d) (x : V) : Nat.card (ClosedNeighbor G x) ≤ d + 1 := by
  change ({y : V | x = y ∨ G.Adj x y} : Set V).ncard ≤ d + 1
  rw [setOf_closedNeighbor_eq_insert, Set.ncard_insert_of_notMem]
  · exact Nat.add_le_add_right (hdegree x) 1
  · simp

/-- A uniform code space with `d + 1` choices at each of `n` stages. -/
def BFSCode (d : ℕ) : ℕ → Type
  | 0 => PUnit
  | n + 1 => Fin (d + 1) × BFSCode d n

/--
@isnad1 id=finite.0h2v.s3.9cd30fe09b5a from=translated src=- shape=b794339c vocab=e7b51e65
-/
instance finite_bfsCode (d n : ℕ) : Finite (BFSCode d n) := by
  induction n with
  | zero => exact inferInstanceAs (Finite PUnit)
  | succ n ih =>
      change Finite (Fin (d + 1) × BFSCode d n)
      let : Finite (BFSCode d n) := ih
      infer_instance

/--
@isnad1 id=eq.0h2v.s5.4d4a707a5d90 from=translated src=- shape=d71eaefc vocab=750663dc
-/
@[simp] lemma natCard_bfsCode (d n : ℕ) : Nat.card (BFSCode d n) = (d + 1) ^ n := by
  induction n with
  | zero => simp [BFSCode]
  | succ n ih => simp [BFSCode, ih, pow_succ, mul_comm]

/-- Exact-length breadth-first routes.  Unlike graph walks, these permit stationary moves. -/
def BFSRouteCode {V : Type u} (G : SimpleGraph V) : V → ℕ → Type u
  | _, 0 => PUnit
  | x, n + 1 => Σ y : ClosedNeighbor G x, BFSRouteCode G y.1 n

/-- The endpoint of a breadth-first route code. -/
def BFSRouteCode.endpoint {V : Type u} (G : SimpleGraph V) :
    {x : V} → {n : ℕ} → BFSRouteCode G x n → V
  | x, 0, _ => x
  | _, _ + 1, c => endpoint G c.2

/-- A graph walk of length at most `n` can be padded by stationary moves to an exact-length
breadth-first route code with the same endpoint.
@isnad1 id=ex.1h6v.s5.46f0c841185a from=translated src=- shape=dbec0537 vocab=12d78f76
-/
lemma exists_bfsRouteCode_endpoint_of_walk {V : Type u} {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) {n : ℕ} (hp : p.length ≤ n) :
    ∃ c : BFSRouteCode G x n, c.endpoint G = y := by
  induction n generalizing x y with
  | zero =>
      have hlen : p.length = 0 := Nat.eq_zero_of_le_zero hp
      have hxy : x = y := p.eq_of_length_eq_zero hlen
      subst y
      exact ⟨PUnit.unit, rfl⟩
  | succ n ih =>
      cases p with
      | nil =>
          obtain ⟨c, hc⟩ := ih (.nil : G.Walk x x) (Nat.zero_le n)
          exact ⟨⟨⟨x, Or.inl rfl⟩, c⟩, hc⟩
      | @cons x z y hxz tail =>
          have htail : tail.length ≤ n := Nat.succ_le_succ_iff.mp hp
          obtain ⟨c, hc⟩ := ih tail htail
          exact ⟨⟨⟨z, Or.inr hxz⟩, c⟩, hc⟩

/-- Each closed neighborhood embeds in the uniform alphabet of size `d + 1`. -/
noncomputable def closedNeighborEmbedding {V : Type u} [Finite V] {G : SimpleGraph V} {d : ℕ}
    (hdegree : MaxDegreeLE G d) (x : V) : ClosedNeighbor G x ↪ Fin (d + 1) :=
  (Finite.equivFin (ClosedNeighbor G x)).toEmbedding.trans
    (Fin.castLEEmb (natCard_closedNeighbor_le hdegree x))

/-- Encode a breadth-first route into a fixed-length word over `Fin (d + 1)`. -/
noncomputable def encodeBFSRoute {V : Type u} [Finite V] {G : SimpleGraph V} {d : ℕ}
    (hdegree : MaxDegreeLE G d) :
    (n : ℕ) → (x : V) → BFSRouteCode G x n → BFSCode d n
  | 0, _, _ => PUnit.unit
  | n + 1, x, c =>
      (closedNeighborEmbedding hdegree x c.1, encodeBFSRoute hdegree n c.1.1 c.2)

/--
@isnad1 id=injectiv.1h5v.s5.8cca34b2142d from=translated src=- shape=3a5b0a0f vocab=1320e6aa
-/
lemma encodeBFSRoute_injective {V : Type u} [Finite V] {G : SimpleGraph V} {d : ℕ}
    (hdegree : MaxDegreeLE G d) (n : ℕ) (x : V) :
    Function.Injective (encodeBFSRoute hdegree n x) := by
  induction n generalizing x with
  | zero =>
      intro a b _
      cases a
      cases b
      rfl
  | succ n ih =>
      rintro ⟨y, c⟩ ⟨z, c'⟩ h
      have hyz : y = z := (closedNeighborEmbedding hdegree x).injective
        (congrArg Prod.fst h)
      subst z
      have htail : encodeBFSRoute hdegree n y.1 c = encodeBFSRoute hdegree n y.1 c' := by
        simpa [encodeBFSRoute] using congrArg Prod.snd h
      have hcc' : c = c' := ih y.1 htail
      subst c'
      rfl

/-- Embed length-n routes into the finite set of degree-bounded BFS codes. -/
noncomputable def bfsRouteEmbedding {V : Type u} [Finite V]
    {G : SimpleGraph V} {d : ℕ} (hdegree : MaxDegreeLE G d) (n : ℕ) (x : V) :
    BFSRouteCode G x n ↪ BFSCode d n :=
  ⟨encodeBFSRoute hdegree n x, encodeBFSRoute_injective hdegree n x⟩

/-- Coarse breadth-first bound.  Its leading term is still `d^k`, so it is sufficient for the
upper asymptotic in Theorem 1.1.
@isnad1 id=le.2h4v.s5.0f57d20bce4b from=translated src=- shape=3dfb9307 vocab=32552859
-/
lemma natCard_le_add_one_pow_of_ediam_le {V : Type u} [Finite V] [Nonempty V]
    {G : SimpleGraph V} {d k : ℕ} (hdegree : MaxDegreeLE G d)
    (hdiam : G.ediam ≤ (k : ℕ∞)) : Nat.card V ≤ (d + 1) ^ k := by
  let root : V := Classical.ofNonempty
  let e := bfsRouteEmbedding hdegree k root
  let : Finite (BFSRouteCode G root k) := Finite.of_injective e e.injective
  have hsurj : Function.Surjective (BFSRouteCode.endpoint G (x := root) (n := k)) := by
    intro y
    have hdist : G.edist root y ≤ (k : ℕ∞) := SimpleGraph.edist_le_ediam.trans hdiam
    have hfinite : G.edist root y ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top k) hdist
    obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hfinite
    have hlength : p.length ≤ k := by
      rw [← hp] at hdist
      exact_mod_cast hdist
    exact exists_bfsRouteCode_endpoint_of_walk p hlength
  calc
    Nat.card V ≤ Nat.card (BFSRouteCode G root k) :=
      Nat.card_le_card_of_surjective _ hsurj
    _ ≤ Nat.card (BFSCode d k) := Nat.card_le_card_of_injective e e.injective
    _ = (d + 1) ^ k := natCard_bfsCode d k

/--
@isnad1 id=le.2h4v.s5.351c8e80a18e from=translated src=- shape=70a07d79 vocab=88785f60
-/
lemma natCard_le_add_one_pow_of_ediam_le' {V : Type u} [Finite V]
    {G : SimpleGraph V} {d k : ℕ} (hdegree : MaxDegreeLE G d)
    (hdiam : G.ediam ≤ (k : ℕ∞)) : Nat.card V ≤ (d + 1) ^ k := by
  cases isEmpty_or_nonempty V
  · simp
  · exact natCard_le_add_one_pow_of_ediam_le hdegree hdiam

/-! ## A coarse degree bound for line graphs -/
/-- Choose the common endpoint of two adjacent edges of the original graph. -/
noncomputable def lineGraphSharedVertex {V : Type u} {G : SimpleGraph V}
    (e : G.edgeSet) (f : G.lineGraph.neighborSet e) : V :=
  Classical.choose (SimpleGraph.lineGraph_adj_iff_exists.mp f.property).2

/--
@isnad1 id=mem.0h4v.s6.ae96aa74f827 from=translated src=- shape=d602bb3c vocab=a211e151
-/
lemma lineGraphSharedVertex_mem_left {V : Type u} {G : SimpleGraph V}
    (e : G.edgeSet) (f : G.lineGraph.neighborSet e) : lineGraphSharedVertex e f ∈ e.1 :=
  (Classical.choose_spec (SimpleGraph.lineGraph_adj_iff_exists.mp f.property).2).1

/--
@isnad1 id=mem.0h4v.s6.ef276462d95e from=translated src=- shape=34d5e5f7 vocab=a211e151
-/
lemma lineGraphSharedVertex_mem_right {V : Type u} {G : SimpleGraph V}
    (e : G.edgeSet) (f : G.lineGraph.neighborSet e) : lineGraphSharedVertex e f ∈ f.1.1 :=
  (Classical.choose_spec (SimpleGraph.lineGraph_adj_iff_exists.mp f.property).2).2

/-- Encode an edge neighboring `e` in the line graph by a shared endpoint of `e` and the other
endpoint of the neighboring edge. -/
noncomputable def lineGraphNeighborCode {V : Type u} {G : SimpleGraph V} (e : G.edgeSet) :
    G.lineGraph.neighborSet e → Σ v : {v : V // v ∈ e.1}, G.neighborSet v.1 :=
  fun f ↦
    let v := lineGraphSharedVertex e f
    let hvf : v ∈ f.1.1 := lineGraphSharedVertex_mem_right e f
    ⟨⟨v, lineGraphSharedVertex_mem_left e f⟩,
      ⟨Sym2.Mem.other hvf, by
        have hedge : s(v, Sym2.Mem.other hvf) ∈ G.edgeSet := by
          rw [Sym2.other_spec hvf]
          exact f.1.2
        exact G.mem_edgeSet.mp hedge⟩⟩

/-- Recover the encoded neighboring edge. -/
def edgeOfLineGraphNeighborCode {V : Type u} {G : SimpleGraph V} {e : G.edgeSet}
    (c : Σ v : {v : V // v ∈ e.1}, G.neighborSet v.1) : G.edgeSet :=
  ⟨s(c.1.1, c.2.1), G.mem_edgeSet.mpr c.2.2⟩

/--
@isnad1 id=eq.0h4v.s6.b8ce6d80a68c from=translated src=- shape=ecf0047a vocab=cbe4189f
-/
lemma edgeOfLineGraphNeighborCode_code {V : Type u} {G : SimpleGraph V}
    (e : G.edgeSet) (f : G.lineGraph.neighborSet e) :
    edgeOfLineGraphNeighborCode (lineGraphNeighborCode e f) = f.1 := by
  apply Subtype.ext
  exact Sym2.other_spec (lineGraphSharedVertex_mem_right e f)

/--
@isnad1 id=injectiv.0h3v.s7.3ff3fd3108f8 from=translated src=- shape=8cf9bcd5 vocab=f0d79bb9
-/
lemma lineGraphNeighborCode_injective {V : Type u} {G : SimpleGraph V} (e : G.edgeSet) :
    Function.Injective (lineGraphNeighborCode e) := by
  intro f g hfg
  apply Subtype.ext
  rw [← edgeOfLineGraphNeighborCode_code e f, ← edgeOfLineGraphNeighborCode_code e g,
    hfg]

/--
@isnad1 id=eq.0h3v.s5.038442576ea1 from=translated src=- shape=37fb1235 vocab=af4b2286
-/
lemma natCard_endpoints_eq_two {V : Type u} {G : SimpleGraph V} (e : G.edgeSet) :
    Nat.card {v : V // v ∈ e.1} = 2 := by
  change (e.1 : Set V).ncard = 2
  let a := e.1.out.1
  let b := e.1.out.2
  have heq : s(a, b) = e.1 := e.1.out_eq
  have hab : a ≠ b := by
    have hadj : G.Adj a b := by
      rw [← G.mem_edgeSet, heq]
      exact e.2
    exact hadj.ne
  rw [← heq, Sym2.coe_mk, Set.ncard_pair hab]

/-- A coarse line-graph maximum-degree bound.  The sharper standard estimate is
`2 * (d - 1)`; `2 * d` is enough to establish finite boundedness of the edge extremum.
@isnad1 id=maxdegre.1h3v.s5.f9978171021a from=translated src=- shape=ebf55037 vocab=5838562e
-/
lemma maxDegreeLE_lineGraph {V : Type u} [Finite V] {G : SimpleGraph V} {d : ℕ}
    (hdegree : MaxDegreeLE G d) : MaxDegreeLE G.lineGraph (2 * d) := by
  intro e
  classical
  let : Fintype V := Fintype.ofFinite V
  let : DecidableRel G.Adj := Classical.decRel G.Adj
  have hcode : Nat.card (G.lineGraph.neighborSet e) ≤
      Nat.card (Σ v : {v : V // v ∈ e.1}, G.neighborSet v.1) :=
    Nat.card_le_card_of_injective (lineGraphNeighborCode e) (lineGraphNeighborCode_injective e)
  calc
    (G.lineGraph.neighborSet e).ncard = Nat.card (G.lineGraph.neighborSet e) :=
      (Nat.card_coe_set_eq _).symm
    _ ≤ Nat.card (Σ v : {v : V // v ∈ e.1}, G.neighborSet v.1) := hcode
    _ = ∑ v : {v : V // v ∈ e.1}, Nat.card (G.neighborSet v.1) := by
      rw [Nat.card_sigma]
    _ ≤ ∑ _v : {v : V // v ∈ e.1}, d := by
      apply Finset.sum_le_sum
      intro v _hv
      rw [Nat.card_coe_set_eq]
      exact hdegree v.1
    _ = Nat.card {v : V // v ∈ e.1} * d := by simp
    _ = 2 * d := by rw [natCard_endpoints_eq_two]

/-- A finite simple graph of order `n`, maximum degree at most `d`, and diameter at most `k`.

The quantified vertex type is kept native instead of transporting every construction to `Fin n`.
`Finite V` makes `Nat.card V` and the set cardinalities mathematically meaningful. -/
noncomputable def OrderAdmissible (k d n : ℕ) : Prop :=
  ∃ (V : Type) (G : SimpleGraph V),
    Finite V ∧ Nat.card V = n ∧ MaxDegreeLE G d ∧ G.ediam ≤ (k : ℕ∞)

/--
@isnad1 id=le.1h3v.s5.4b3753c6e1c7 from=translated src=- shape=4f2a1b90 vocab=3506fd6a
-/
lemma orderAdmissible_le_coarseBound {k d n : ℕ} (hn : OrderAdmissible k d n) :
    n ≤ (d + 1) ^ k := by
  rcases hn with ⟨V, G, hfinite, hcard, hdegree, hdiam⟩
  let : Finite V := hfinite
  rw [← hcard]
  exact natCard_le_add_one_pow_of_ediam_le' hdegree hdiam

/-- The defining set for `nKD` is bounded, unconditionally.
@isnad1 id=bddabove.0h2v.s3.45d98c517361 from=translated src=- shape=ec408e4a vocab=4270c6e3
-/
lemma orderAdmissible_set_bddAbove (k d : ℕ) :
    BddAbove {n : ℕ | OrderAdmissible k d n} :=
  ⟨(d + 1) ^ k, fun _ hn ↦ orderAdmissible_le_coarseBound hn⟩

/-- The degree--diameter extremal order.  The specification lemmas below require (and later the
Moore bound supplies) boundedness of the defining set. -/
noncomputable def nKD (k d : ℕ) : ℕ :=
  sSup {n : ℕ | OrderAdmissible k d n}

/-- A finite simple graph with `m` edges, maximum degree at most `d`, and line-graph diameter at
most `ell`. -/
noncomputable def EdgeAdmissible (ell d m : ℕ) : Prop :=
  ∃ (V : Type) (G : SimpleGraph V),
    Finite V ∧ G.edgeSet.ncard = m ∧ MaxDegreeLE G d ∧
      G.lineGraph.ediam ≤ (ell : ℕ∞)

/--
@isnad1 id=le.1h3v.s5.6f2897300024 from=translated src=- shape=37150195 vocab=8301c9f6
-/
lemma edgeAdmissible_le_coarseBound {ell d m : ℕ} (hm : EdgeAdmissible ell d m) :
    m ≤ (2 * d + 1) ^ ell := by
  rcases hm with ⟨V, G, hfinite, hcard, hdegree, hdiam⟩
  let : Finite V := hfinite
  let : Finite G.edgeSet := Finite.of_injective Subtype.val Subtype.val_injective
  rw [← hcard]
  calc
    G.edgeSet.ncard = Nat.card G.edgeSet := (Nat.card_coe_set_eq _).symm
    _ ≤ (2 * d + 1) ^ ell :=
      natCard_le_add_one_pow_of_ediam_le' (maxDegreeLE_lineGraph hdegree) hdiam

/-- The defining edge-count set is bounded, unconditionally.
@isnad1 id=bddabove.0h2v.s3.f0ab15af1244 from=translated src=- shape=ec408e4a vocab=b88f33e2
-/
lemma edgeAdmissible_set_bddAbove (ell d : ℕ) :
    BddAbove {m : ℕ | EdgeAdmissible ell d m} :=
  ⟨(2 * d + 1) ^ ell, fun _ hm ↦ edgeAdmissible_le_coarseBound hm⟩

/-- The paper defines `h_ell(d) - 1` as the maximum admissible edge count, so we define `h` to be
one plus that maximum. -/
noncomputable def h (ell d : ℕ) : ℕ :=
  1 + sSup {m : ℕ | EdgeAdmissible ell d m}

/-- The exact Moore expression. -/
def mooreBound (k d : ℕ) : ℕ :=
  1 + d * ∑ j ∈ Finset.range k, (d - 1) ^ j

/--
@isnad1 id=maxdegre.2h4v.s4.6f4030e6e545 from=translated src=- shape=2c4e7a9e vocab=33286d7f
-/
lemma maxDegreeLE_mono {V : Type*} {G : SimpleGraph V} {d d' : ℕ}
    (hdd' : d ≤ d') (hG : MaxDegreeLE G d) : MaxDegreeLE G d' :=
  fun v ↦ (hG v).trans hdd'

/--
@isnad1 id=orderadm.2h4v.s4.c6a82ce2a3ef from=translated src=- shape=699f97bb vocab=ec3465c7
-/
lemma orderAdmissible_mono_degree {k d d' n : ℕ} (hdd' : d ≤ d')
    (hn : OrderAdmissible k d n) : OrderAdmissible k d' n := by
  rcases hn with ⟨V, G, hV, hcard, hdeg, hdiam⟩
  exact ⟨V, G, hV, hcard, maxDegreeLE_mono hdd' hdeg, hdiam⟩

/--
@isnad1 id=orderadm.2h4v.s4.74004be5ffae from=translated src=- shape=a28b0d7f vocab=ec3465c7
-/
lemma orderAdmissible_mono_diameter {k k' d n : ℕ} (hkk' : k ≤ k')
    (hn : OrderAdmissible k d n) : OrderAdmissible k' d n := by
  rcases hn with ⟨V, G, hV, hcard, hdeg, hdiam⟩
  exact ⟨V, G, hV, hcard, hdeg, hdiam.trans (by exact_mod_cast hkk')⟩

/--
@isnad1 id=edgeadmi.2h4v.s4.e4e1e6fdcf5e from=translated src=- shape=699f97bb vocab=41aa12bb
-/
lemma edgeAdmissible_mono_degree {ell d d' m : ℕ} (hdd' : d ≤ d')
    (hm : EdgeAdmissible ell d m) : EdgeAdmissible ell d' m := by
  rcases hm with ⟨V, G, hV, hcard, hdeg, hdiam⟩
  exact ⟨V, G, hV, hcard, maxDegreeLE_mono hdd' hdeg, hdiam⟩

/--
@isnad1 id=edgeadmi.2h4v.s4.a1112b6eca86 from=translated src=- shape=a28b0d7f vocab=41aa12bb
-/
lemma edgeAdmissible_mono_diameter {ell ell' d m : ℕ} (hell : ell ≤ ell')
    (hm : EdgeAdmissible ell d m) : EdgeAdmissible ell' d m := by
  rcases hm with ⟨V, G, hV, hcard, hdeg, hdiam⟩
  exact ⟨V, G, hV, hcard, hdeg, hdiam.trans (by exact_mod_cast hell)⟩

/-- The admissible-order set is always nonempty; the one-vertex edgeless graph is a witness.
@isnad1 id=nonempty.0h2v.s3.3806591f3298 from=translated src=- shape=ec408e4a vocab=0316a50a
-/
lemma orderAdmissible_set_nonempty (k d : ℕ) :
    ({n : ℕ | OrderAdmissible k d n} : Set ℕ).Nonempty := by
  refine ⟨1, Unit, (⊥ : SimpleGraph Unit), inferInstance, ?_, ?_, ?_⟩
  · simp
  · intro v
    simp
  · calc
      (⊥ : SimpleGraph Unit).ediam = 0 := SimpleGraph.ediam_eq_zero_of_subsingleton
      _ ≤ (k : ℕ∞) := bot_le

/-- The admissible-edge-count set is always nonempty; an edgeless graph is a witness.
@isnad1 id=nonempty.0h2v.s3.0058d1ad7343 from=translated src=- shape=ec408e4a vocab=2e62238a
-/
lemma edgeAdmissible_set_nonempty (ell d : ℕ) :
    ({m : ℕ | EdgeAdmissible ell d m} : Set ℕ).Nonempty := by
  refine ⟨0, Unit, (⊥ : SimpleGraph Unit), inferInstance, ?_, ?_, ?_⟩
  · simp
  · intro v
    simp
  · calc
      (⊥ : SimpleGraph Unit).lineGraph.ediam = 0 :=
        SimpleGraph.ediam_eq_zero_of_subsingleton
      _ ≤ (ell : ℕ∞) := bot_le

/-- Any admissible order is at most the extremal value, once boundedness has been established.
@isnad1 id=le.2h3v.s4.c5d0f50121af from=translated src=- shape=5ab49c9f vocab=9ae1028c
-/
lemma le_nKD_of_bddAbove {k d n : ℕ}
    (hbdd : BddAbove {n : ℕ | OrderAdmissible k d n})
    (hn : OrderAdmissible k d n) : n ≤ nKD k d := by
  exact le_csSup hbdd hn

/-- Under boundedness, `nKD` is itself attained by a finite simple graph.
@isnad1 id=orderadm.1h2v.s4.251527ee61cd from=translated src=- shape=f1f31f79 vocab=26f074f5
-/
lemma nKD_admissible_of_bddAbove (k d : ℕ)
    (hbdd : BddAbove {n : ℕ | OrderAdmissible k d n}) :
    OrderAdmissible k d (nKD k d) := by
  exact Nat.sSup_mem (orderAdmissible_set_nonempty k d) hbdd

/-- Conditional maximum specification for `nKD`.
@isnad1 id=isgreate.1h2v.s4.54039bd3ec31 from=translated src=- shape=f9d40863 vocab=43c506e8
-/
lemma nKD_isGreatest_of_bddAbove (k d : ℕ)
    (hbdd : BddAbove {n : ℕ | OrderAdmissible k d n}) :
    IsGreatest {n : ℕ | OrderAdmissible k d n} (nKD k d) := by
  refine ⟨nKD_admissible_of_bddAbove k d hbdd, ?_⟩
  intro n hn
  exact le_nKD_of_bddAbove hbdd hn

/-- Unconditional extremal specification, using the coarse breadth-first bound above.
@isnad1 id=le.1h3v.s4.d37445e7cd0a from=translated src=- shape=be41f538 vocab=3c964be8
-/
lemma le_nKD {k d n : ℕ} (hn : OrderAdmissible k d n) : n ≤ nKD k d :=
  le_nKD_of_bddAbove (orderAdmissible_set_bddAbove k d) hn

/--
@isnad1 id=orderadm.0h2v.s3.f23051bd259d from=translated src=- shape=c08a1264 vocab=4d5095c2
-/
lemma nKD_admissible (k d : ℕ) : OrderAdmissible k d (nKD k d) :=
  nKD_admissible_of_bddAbove k d (orderAdmissible_set_bddAbove k d)

/--
@isnad1 id=isgreate.0h2v.s4.797151cb0719 from=translated src=- shape=bca60147 vocab=e6c7e154
-/
lemma nKD_isGreatest (k d : ℕ) :
    IsGreatest {n : ℕ | OrderAdmissible k d n} (nKD k d) :=
  nKD_isGreatest_of_bddAbove k d (orderAdmissible_set_bddAbove k d)

/-- Any admissible edge count is at most `h ell d - 1`, once boundedness has been established.
@isnad1 id=le.2h3v.s5.f7994fc3fd0f from=translated src=- shape=43f8a8ac vocab=73c36875
-/
lemma le_h_sub_one_of_bddAbove {ell d m : ℕ}
    (hbdd : BddAbove {m : ℕ | EdgeAdmissible ell d m})
    (hm : EdgeAdmissible ell d m) : m ≤ h ell d - 1 := by
  have hm' : m ≤ sSup {m : ℕ | EdgeAdmissible ell d m} := le_csSup hbdd hm
  simpa [h] using hm'

/-- Under boundedness, `h ell d - 1` is itself attained.
@isnad1 id=edgeadmi.1h2v.s5.c48674e30526 from=translated src=- shape=65d9fe62 vocab=5718b5be
-/
lemma h_sub_one_admissible_of_bddAbove (ell d : ℕ)
    (hbdd : BddAbove {m : ℕ | EdgeAdmissible ell d m}) :
    EdgeAdmissible ell d (h ell d - 1) := by
  have hs : EdgeAdmissible ell d (sSup {m : ℕ | EdgeAdmissible ell d m}) :=
    Nat.sSup_mem (edgeAdmissible_set_nonempty ell d) hbdd
  simpa [h] using hs

/-- Conditional maximum specification for the paper's edge extremum `h ell d - 1`.
@isnad1 id=isgreate.1h2v.s5.8c3bfa401ec1 from=translated src=- shape=d684a164 vocab=b9228f60
-/
lemma h_sub_one_isGreatest_of_bddAbove (ell d : ℕ)
    (hbdd : BddAbove {m : ℕ | EdgeAdmissible ell d m}) :
    IsGreatest {m : ℕ | EdgeAdmissible ell d m} (h ell d - 1) := by
  refine ⟨h_sub_one_admissible_of_bddAbove ell d hbdd, ?_⟩
  intro m hm
  exact le_h_sub_one_of_bddAbove hbdd hm

/-- Unconditional edge-extremum specifications, using the coarse line-graph bound above.
@isnad1 id=le.1h3v.s4.678c5afc85b5 from=translated src=- shape=909ef7ce vocab=f6b8c551
-/
lemma le_h_sub_one {ell d m : ℕ} (hm : EdgeAdmissible ell d m) : m ≤ h ell d - 1 :=
  le_h_sub_one_of_bddAbove (edgeAdmissible_set_bddAbove ell d) hm

/--
@isnad1 id=edgeadmi.0h2v.s4.fb1c735202d5 from=translated src=- shape=c83c0f9e vocab=e3db558c
-/
lemma h_sub_one_admissible (ell d : ℕ) : EdgeAdmissible ell d (h ell d - 1) :=
  h_sub_one_admissible_of_bddAbove ell d (edgeAdmissible_set_bddAbove ell d)

/--
@isnad1 id=isgreate.0h2v.s4.c7bfff5755f9 from=translated src=- shape=bf6882b5 vocab=0d222d77
-/
lemma h_sub_one_isGreatest (ell d : ℕ) :
    IsGreatest {m : ℕ | EdgeAdmissible ell d m} (h ell d - 1) :=
  h_sub_one_isGreatest_of_bddAbove ell d (edgeAdmissible_set_bddAbove ell d)

/--
@isnad1 id=le.0h2v.s5.437930823367 from=translated src=- shape=582ea08b vocab=cbb2820b
-/
lemma h_sub_one_le_coarseBound (ell d : ℕ) : h ell d - 1 ≤ (2 * d + 1) ^ ell :=
  edgeAdmissible_le_coarseBound (h_sub_one_admissible ell d)

end DegreeDiameter

end MooreBound
