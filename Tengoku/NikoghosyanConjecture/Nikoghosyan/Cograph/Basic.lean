/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku.Seed.Combinatorics.SimpleGraph.Basic
import Tengoku.Seed.Combinatorics.SimpleGraph.Connectivity.Connected
import Tengoku.Seed.Combinatorics.SimpleGraph.Connectivity.Finite
import Tengoku.Seed.Combinatorics.SimpleGraph.Diam
import Tengoku.Seed.Combinatorics.SimpleGraph.Finite
import Tengoku.Seed.Combinatorics.SimpleGraph.Maps
import Tengoku.Seed.Combinatorics.SimpleGraph.Metric
import Tengoku.Seed.Combinatorics.SimpleGraph.Operations
import Tengoku.Seed.Combinatorics.SimpleGraph.Paths
import Tengoku.Seed.Data.Fintype.Card
import Tengoku.Seed.Data.Fintype.Powerset
import Tengoku.Seed.Data.Finset.Card
import Tengoku.Seed.Data.Set.Card
import Tengoku.Seed.Data.Set.Finite.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cograph primitives for the Nikoghosyan formalization

These definitions match the approved Phase-1 interface in `FORMALIZATION_PLAN.md`:
an induced `P4` is four distinct vertices with the three path edges and the three
missing chords; a cograph on a vertex set is the absence of such a quadruple
inside that set. A cotree is *not* used as a hypothesis here.

This module is self-contained on Mathlib `SimpleGraph`. It does not import
`Nikoghosyan.Basic`; when that foundation module is published, the signatures
here should be aligned and re-exported rather than duplicated.
-/

universe u

namespace Nikoghosyan
namespace Cograph

open scoped Classical
open SimpleGraph

variable {V : Type u}

/-- Four distinct vertices induce a `P4` in path order `a-b-c-d`.-/
structure InducedP4 (G : SimpleGraph V) (a b c d : V) : Prop where
  ne_ab : a ≠ b
  ne_ac : a ≠ c
  ne_ad : a ≠ d
  ne_bc : b ≠ c
  ne_bd : b ≠ d
  ne_cd : c ≠ d
  adj_ab : G.Adj a b
  adj_bc : G.Adj b c
  adj_cd : G.Adj c d
  not_ac : ¬ G.Adj a c
  not_ad : ¬ G.Adj a d
  not_bd : ¬ G.Adj b d

namespace InducedP4

variable {G : SimpleGraph V} {a b c d : V}

/--
@isnad1 id=and.1h6v.s5.34aeab4e1d18 from=translated src=- shape=9bc8097f vocab=10cda62a
-/
lemma pairwise_ne (h : InducedP4 G a b c d) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d :=
  ⟨h.ne_ab, h.ne_ac, h.ne_ad, h.ne_bc, h.ne_bd, h.ne_cd⟩

/-- Reversing the path order yields another induced `P4`.
@isnad1 id=inducedp.1h6v.s4.b0345eeb1c43 from=translated src=- shape=59dccae5 vocab=10cda62a
-/
lemma reverse (h : InducedP4 G a b c d) : InducedP4 G d c b a where
  ne_ab := h.ne_cd.symm
  ne_ac := h.ne_bd.symm
  ne_ad := h.ne_ad.symm
  ne_bc := h.ne_bc.symm
  ne_bd := h.ne_ac.symm
  ne_cd := h.ne_ab.symm
  adj_ab := h.adj_cd.symm
  adj_bc := h.adj_bc.symm
  adj_cd := h.adj_ab.symm
  not_ac := (h.not_bd <| ·.symm)
  not_ad := (h.not_ad <| ·.symm)
  not_bd := (h.not_ac <| ·.symm)

/--
@isnad1 id=eq.1h6v.s6.622c95bfda56 from=translated src=- shape=2f015fa0 vocab=1dcb4bca
-/
lemma card_four [DecidableEq V] (h : InducedP4 G a b c d) :
    ({a, b, c, d} : Finset V).card = 4 := by
  have had : a ∉ ({b, c, d} : Finset V) := by simp [h.ne_ab, h.ne_ac, h.ne_ad]
  have hbd : b ∉ ({c, d} : Finset V) := by simp [h.ne_bc, h.ne_bd]
  have hcd : c ∉ ({d} : Finset V) := by simp [h.ne_cd]
  simp [Finset.card_insert_of_notMem, had, hbd, hcd]

/--
@isnad1 id=adj.1h6v.s4.b4da234a4b7b from=translated src=- shape=8366f539 vocab=0f9153d5
-/
lemma adj_ab_of (h : InducedP4 G a b c d) : G.Adj a b := h.adj_ab
/--
@isnad1 id=adj.1h6v.s4.49cd1adf6d0f from=translated src=- shape=6542e54c vocab=0f9153d5
-/
lemma adj_bc_of (h : InducedP4 G a b c d) : G.Adj b c := h.adj_bc
/--
@isnad1 id=adj.1h6v.s4.76a473f6468b from=translated src=- shape=88a8116e vocab=0f9153d5
-/
lemma adj_cd_of (h : InducedP4 G a b c d) : G.Adj c d := h.adj_cd

/-- No vertex of an induced `P4` is adjacent to the other three vertices.
@isnad1 id=not.2h7v.s6.308ab9d0f590 from=translated src=- shape=71669604 vocab=0f9153d5
-/
lemma not_adj_other_three (h : InducedP4 G a b c d) {x : V}
    (hx : x = a ∨ x = b ∨ x = c ∨ x = d) :
    ¬ ((x ≠ a → G.Adj x a) ∧ (x ≠ b → G.Adj x b) ∧
        (x ≠ c → G.Adj x c) ∧ (x ≠ d → G.Adj x d)) := by
  rintro ⟨ha, hb, hc, hd⟩
  rcases hx with hx | hx | hx | hx
  · exact h.not_ac <| hx ▸ hc (hx ▸ h.ne_ac)
  · exact h.not_bd <| hx ▸ hd (hx ▸ h.ne_bd)
  · exact h.not_ac <| hx ▸ (ha (hx ▸ h.ne_ac.symm)).symm
  · exact h.not_bd <| hx ▸ (hb (hx ▸ h.ne_bd.symm)).symm

end InducedP4

/-- Absence of an induced `P4` with all four vertices in `U`.-/
def IsCograph (G : SimpleGraph V) (U : Finset V) : Prop :=
  ∀ ⦃a b c d : V⦄, a ∈ U → b ∈ U → c ∈ U → d ∈ U → ¬ InducedP4 G a b c d

/-- Set-valued form of `IsCograph`.-/
def IsCographOn (G : SimpleGraph V) (U : Set V) : Prop :=
  ∀ ⦃a b c d : V⦄, a ∈ U → b ∈ U → c ∈ U → d ∈ U → ¬ InducedP4 G a b c d

/-- The whole graph is a cograph.-/
def IsCographGraph (G : SimpleGraph V) : Prop :=
  ∀ a b c d : V, ¬ InducedP4 G a b c d

/-- No induced `P4 ∪ P1`: every vertex outside an induced `P4` meets that `P4`.
The isolated vertex is required to be distinct from the four path vertices.-/
def NoInducedP4UnionP1 (G : SimpleGraph V) : Prop :=
  ∀ ⦃a b c d x : V⦄, InducedP4 G a b c d →
    x ≠ a → x ≠ b → x ≠ c → x ≠ d →
    G.Adj x a ∨ G.Adj x b ∨ G.Adj x c ∨ G.Adj x d

/--
@isnad1 id=iff.0h3v.s4.a5d937b79045 from=translated src=- shape=5528a77e vocab=f47fbb10
-/
lemma isCographOn_iff_isCograph {G : SimpleGraph V} {U : Finset V} :
    IsCographOn G U ↔ IsCograph G U :=
  Iff.rfl

/--
@isnad1 id=iff.0h2v.s4.38b1a317f20e from=translated src=- shape=f5a701d4 vocab=c57e02d1
-/
lemma isCographGraph_iff_univ [Fintype V] {G : SimpleGraph V} :
    IsCographGraph G ↔ IsCograph G Finset.univ := by
  constructor
  · intro h a b c d _ _ _ _ hp
    exact h a b c d hp
  · intro h a b c d hp
    exact h (Finset.mem_univ a) (Finset.mem_univ b) (Finset.mem_univ c) (Finset.mem_univ d) hp

/--
@isnad1 id=iff.0h2v.s3.31fbc6388a48 from=translated src=- shape=a378c66c vocab=4802c837
-/
lemma isCographGraph_iff_univ_set {G : SimpleGraph V} :
    IsCographGraph G ↔ IsCographOn G Set.univ := by
  constructor
  · intro h a b c d _ _ _ _ hp
    exact h a b c d hp
  · intro h a b c d hp
    exact h (Set.mem_univ a) (Set.mem_univ b) (Set.mem_univ c) (Set.mem_univ d) hp

/-- Induced inheritance: subsets of a cograph vertex set remain cographs.
@isnad1 id=iscograp.2h4v.s5.53f48b011dda from=translated src=- shape=68aab49f vocab=548e8d5f
-/
lemma isCograph_mono {G : SimpleGraph V} {U W : Finset V}
    (hW : IsCograph G W) (hUW : U ⊆ W) : IsCograph G U :=
  fun _ _ _ _ ha hb hc hd hp =>
    hW (hUW ha) (hUW hb) (hUW hc) (hUW hd) hp

/--
@isnad1 id=iscograp.2h4v.s4.959c8ec3651d from=translated src=- shape=68aab49f vocab=afd2b974
-/
lemma isCographOn_mono {G : SimpleGraph V} {U W : Set V}
    (hW : IsCographOn G W) (hUW : U ⊆ W) : IsCographOn G U :=
  fun _ _ _ _ ha hb hc hd hp =>
    hW (hUW ha) (hUW hb) (hUW hc) (hUW hd) hp

/--
@isnad1 id=iscograp.1h3v.s4.82f8f3c2759f from=translated src=- shape=1b90ed26 vocab=f6a52d78
-/
lemma isCographOn_of_isCographGraph {G : SimpleGraph V} (h : IsCographGraph G) (U : Set V) :
    IsCographOn G U :=
  fun _ _ _ _ _ _ _ _ hp => h _ _ _ _ hp

/--
@isnad1 id=iscograp.1h3v.s4.95c8ec111283 from=translated src=- shape=1b90ed26 vocab=85cccb0a
-/
lemma isCograph_of_isCographGraph {G : SimpleGraph V} (h : IsCographGraph G) (U : Finset V) :
    IsCograph G U :=
  fun _ _ _ _ _ _ _ _ hp => h _ _ _ _ hp

/--
@isnad1 id=inducedp.1h7v.s6.92de82dde862 from=translated src=- shape=651d8e24 vocab=86a8749f
-/
lemma inducedP4_induce {G : SimpleGraph V} {s : Set V} {a b c d : s}
    (h : InducedP4 (G.induce s) a b c d) : InducedP4 G a.1 b.1 c.1 d.1 where
  ne_ab := by intro h'; exact h.ne_ab (Subtype.ext h')
  ne_ac := by intro h'; exact h.ne_ac (Subtype.ext h')
  ne_ad := by intro h'; exact h.ne_ad (Subtype.ext h')
  ne_bc := by intro h'; exact h.ne_bc (Subtype.ext h')
  ne_bd := by intro h'; exact h.ne_bd (Subtype.ext h')
  ne_cd := by intro h'; exact h.ne_cd (Subtype.ext h')
  adj_ab := by simpa [induce_adj] using h.adj_ab
  adj_bc := by simpa [induce_adj] using h.adj_bc
  adj_cd := by simpa [induce_adj] using h.adj_cd
  not_ac := by simpa [induce_adj] using h.not_ac
  not_ad := by simpa [induce_adj] using h.not_ad
  not_bd := by simpa [induce_adj] using h.not_bd

/--
@isnad1 id=inducedp.1h7v.s6.430c522f12d1 from=translated src=- shape=77db54c6 vocab=86a8749f
-/
lemma inducedP4_of_coe {G : SimpleGraph V} {s : Set V} {a b c d : s}
    (h : InducedP4 G a.1 b.1 c.1 d.1) : InducedP4 (G.induce s) a b c d where
  ne_ab := fun h' => h.ne_ab (congrArg Subtype.val h')
  ne_ac := fun h' => h.ne_ac (congrArg Subtype.val h')
  ne_ad := fun h' => h.ne_ad (congrArg Subtype.val h')
  ne_bc := fun h' => h.ne_bc (congrArg Subtype.val h')
  ne_bd := fun h' => h.ne_bd (congrArg Subtype.val h')
  ne_cd := fun h' => h.ne_cd (congrArg Subtype.val h')
  adj_ab := by simpa [induce_adj] using h.adj_ab
  adj_bc := by simpa [induce_adj] using h.adj_bc
  adj_cd := by simpa [induce_adj] using h.adj_cd
  not_ac := by simpa [induce_adj] using h.not_ac
  not_ad := by simpa [induce_adj] using h.not_ad
  not_bd := by simpa [induce_adj] using h.not_bd

/-- Induced subgraphs of a cograph are cographs.
@isnad1 id=iscograp.1h3v.s4.46a6aa42957d from=translated src=- shape=220f91dc vocab=4b4b2027
-/
lemma isCographGraph_induce {G : SimpleGraph V} {s : Set V}
    (h : IsCographGraph G) : IsCographGraph (G.induce s) := by
  intro a b c d hp
  exact h a.1 b.1 c.1 d.1 (inducedP4_induce hp)

/--
@isnad1 id=iff.0h3v.s4.3d5fc41ce0c1 from=translated src=- shape=ba53e436 vocab=d925edfc
-/
lemma isCographOn_iff_isCographGraph_induce {G : SimpleGraph V} {s : Set V} :
    IsCographOn G s ↔ IsCographGraph (G.induce s) := by
  constructor
  · intro h a b c d hp
    exact h a.2 b.2 c.2 d.2 (inducedP4_induce hp)
  · intro h a b c d ha hb hc hd hp
    exact h ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩ (inducedP4_of_coe hp)

/--
@isnad1 id=not.1h6v.s5.358d4307c644 from=translated src=- shape=55db8764 vocab=57fe83e7
-/
lemma not_inducedP4_of_card_lt [Fintype V] {G : SimpleGraph V}
    (hV : Fintype.card V < 4) (a b c d : V) : ¬ InducedP4 G a b c d := by
  intro hp
  classical
  have : 4 ≤ Fintype.card V := by
    have hsubset : ({a, b, c, d} : Finset V) ⊆ Finset.univ := by simp
    have := Finset.card_le_card hsubset
    simpa [hp.card_four] using this
  omega

/--
@isnad1 id=iscograp.1h2v.s4.9b7e45d10ae6 from=translated src=- shape=c355691e vocab=eb2dadb1
-/
lemma isCographGraph_of_card_lt_four [Fintype V] {G : SimpleGraph V}
    (hV : Fintype.card V < 4) : IsCographGraph G :=
  fun a b c d => not_inducedP4_of_card_lt hV a b c d

/--
@isnad1 id=iscograp.1h2v.s4.a0ad1b4e81ec from=translated src=- shape=c355691e vocab=2a6e3a0c
-/
lemma isCographGraph_of_card_le_one [Fintype V] {G : SimpleGraph V}
    (hV : Fintype.card V ≤ 1) : IsCographGraph G :=
  isCographGraph_of_card_lt_four (lt_of_le_of_lt hV (by decide : (1 : ℕ) < 4))

/-! ## Shortest paths and diameter -/

variable {G : SimpleGraph V}

/-- On a shortest `u–w` walk, vertices at index distance at least two are nonadjacent.
@isnad1 id=not.4h7v.s6.d4a903ad76bb from=translated src=- shape=e2a1d555 vocab=65bcb538
-/
lemma not_adj_getVert_of_length_eq_dist {u w : V} {p : G.Walk u w}
    (hp : p.length = G.dist u w) {i j : ℕ}
    (hi : i ≤ p.length) (hj : j ≤ p.length) (hgap : i + 2 ≤ j) :
    ¬ G.Adj (p.getVert i) (p.getVert j) := by
  intro hadj
  let q : G.Walk u w :=
    ((p.take i).append hadj.toWalk).append (p.drop j)
  have hlen : q.length = i + 1 + (p.length - j) := by
    simp [q, Walk.length_append, Walk.take_length, Walk.drop_length, Adj.toWalk,
      Walk.length_cons, hi]
  have hlt : q.length < p.length := by
    have hj' : j ≤ p.length := hj
    have : i + 1 + (p.length - j) < p.length := by
      have : i + 1 < j := Nat.lt_of_succ_le (by omega)
      have hsub : p.length - j + j = p.length := Nat.sub_add_cancel hj'
      omega
    simpa [hlen] using this
  have : G.dist u w ≤ q.length := dist_le q
  omega

/-- The first four vertices of a shortest path of length at least three induce a `P4`.
@isnad1 id=inducedp.2h5v.s6.bdbc9707d450 from=translated src=- shape=28f14928 vocab=71bb3179
-/
lemma inducedP4_of_shortest_path {u w : V} {p : G.Walk u w}
    (hp : p.length = G.dist u w) (h3 : 3 ≤ p.length) :
    InducedP4 G (p.getVert 0) (p.getVert 1) (p.getVert 2) (p.getVert 3) := by
  have hpath : p.IsPath := p.isPath_of_length_eq_dist hp
  have hle3 : 3 ≤ p.length := h3
  have hle i (hi : i ≤ 3) : i ≤ p.length := le_trans hi hle3
  have hne {i j : ℕ} (hi : i ≤ 3) (hj : j ≤ 3) (hij : i ≠ j) :
      p.getVert i ≠ p.getVert j := by
    intro h
    have := hpath.getVert_injOn (by simp [hle i hi]) (by simp [hle j hj]) h
    exact hij this
  refine
    { ne_ab := hne (by decide) (by decide) (by decide)
      ne_ac := hne (by decide) (by decide) (by decide)
      ne_ad := hne (by decide) (by decide) (by decide)
      ne_bc := hne (by decide) (by decide) (by decide)
      ne_bd := hne (by decide) (by decide) (by decide)
      ne_cd := hne (by decide) (by decide) (by decide)
      adj_ab := p.adj_getVert_succ (by omega)
      adj_bc := p.adj_getVert_succ (by omega)
      adj_cd := p.adj_getVert_succ (by omega)
      not_ac := not_adj_getVert_of_length_eq_dist hp (hle 0 (by decide)) (hle 2 (by decide))
                  (by decide)
      not_ad := not_adj_getVert_of_length_eq_dist hp (hle 0 (by decide)) (hle 3 (by decide))
                  (by decide)
      not_bd := not_adj_getVert_of_length_eq_dist hp (hle 1 (by decide)) (hle 3 (by decide))
                  (by decide) }

/-- A connected cograph has ordinary distance at most two.
@isnad1 id=le.2h4v.s4.29d9852ba2b6 from=translated src=- shape=5eb25cbd vocab=819b7764
-/
lemma dist_le_two_of_connected_cograph (hG : G.Connected) (hC : IsCographGraph G)
    (u v : V) : G.dist u v ≤ 2 := by
  by_contra h
  have h3 : 3 ≤ G.dist u v := Nat.succ_le_of_lt (Nat.not_le.mp h)
  obtain ⟨p, -, hp⟩ := hG.exists_path_of_dist u v
  have : InducedP4 G (p.getVert 0) (p.getVert 1) (p.getVert 2) (p.getVert 3) :=
    inducedP4_of_shortest_path hp (by omega)
  exact hC _ _ _ _ this

/-- A connected cograph has extended diameter at most two.
@isnad1 id=le.2h2v.s4.2321e308039f from=translated src=- shape=398a625d vocab=23fd43b3
-/
lemma ediam_le_two_of_connected_cograph (hG : G.Connected) (hC : IsCographGraph G) :
    G.ediam ≤ 2 := by
  refine ediam_le_of_edist_le ?_
  intro u v
  have hr : G.Reachable u v := hG u v
  have hdist : G.dist u v ≤ 2 := dist_le_two_of_connected_cograph hG hC u v
  have : (G.dist u v : ℕ∞) ≤ 2 := Nat.cast_le.mpr hdist
  rwa [hr.coe_dist_eq_edist] at this

/-! ## `P4 ∪ P1` domination and antineighborhoods -/

/-- In a co-gem-free graph, every induced `P4` dominates every other vertex.
@isnad1 id=or.3h7v.s6.0e612c87a14e from=translated src=- shape=fbbe1942 vocab=d44fd0cb
-/
lemma inducedP4_dominates_of_no_p4_union_p1 (h : NoInducedP4UnionP1 G)
    {a b c d x : V} (hp : InducedP4 G a b c d)
    (hx : x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ x ≠ d) :
    G.Adj x a ∨ G.Adj x b ∨ G.Adj x c ∨ G.Adj x d :=
  h hp hx.1 hx.2.1 hx.2.2.1 hx.2.2.2

/-- Closed-neighborhood complement: vertices other than `v` nonadjacent to `v`.-/
def antineighborhood (G : SimpleGraph V) (v : V) : Set V :=
  {w | w ≠ v ∧ ¬ G.Adj v w}

/--
@isnad1 id=iff.0h4v.s5.f591962ceecc from=translated src=- shape=6cfaf33e vocab=127fd8d6
-/
lemma mem_antineighborhood {v w : V} :
    w ∈ antineighborhood G v ↔ w ≠ v ∧ ¬ G.Adj v w :=
  Iff.rfl

/-- Every vertex antineighborhood of a co-gem-free graph is a cograph.
@isnad1 id=iscograp.1h3v.s4.296b06e9ae50 from=translated src=- shape=d5566317 vocab=48b93c74
-/
lemma isCographOn_antineighborhood_of_no_p4_union_p1
    (h : NoInducedP4UnionP1 G) (v : V) :
    IsCographOn G (antineighborhood G v) := by
  intro a b c d ha hb hc hd hp
  have hv : v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ v ≠ d := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact ha.1.symm
    · exact hb.1.symm
    · exact hc.1.symm
    · exact hd.1.symm
  have hmeet := h hp hv.1 hv.2.1 hv.2.2.1 hv.2.2.2
  rcases hmeet with hva | hvb | hvc | hvd
  · exact ha.2 hva
  · exact hb.2 hvb
  · exact hc.2 hvc
  · exact hd.2 hvd

/-- The underlying vertex set of a connected component of an induced subgraph.-/
def componentVerts {s : Set V} (C : (G.induce s).ConnectedComponent) : Set V :=
  Subtype.val '' (C.supp : Set s)

/--
@isnad1 id=iff.0h5v.s6.29236ef02c63 from=translated src=- shape=bc04740d vocab=ea5b7678
-/
lemma mem_componentVerts {s : Set V} {C : (G.induce s).ConnectedComponent} {x : V} :
    x ∈ componentVerts C ↔ ∃ hx : x ∈ s, (⟨x, hx⟩ : s) ∈ C.supp := by
  constructor
  · intro hx
    obtain ⟨⟨x', hx'⟩, hmem, rfl⟩ := hx
    exact ⟨hx', hmem⟩
  · intro ⟨hx, hmem⟩
    exact ⟨⟨x, hx⟩, hmem, rfl⟩

/--
@isnad1 id=le.0h4v.s4.dc29f02c6653 from=translated src=- shape=294df098 vocab=74ddb968
-/
lemma componentVerts_subset {s : Set V} (C : (G.induce s).ConnectedComponent) :
    componentVerts C ⊆ s := by
  intro x hx
  obtain ⟨hx', _⟩ := (mem_componentVerts (C := C)).1 hx
  exact hx'

/-- A vertex outside a component of `G.induce s` is `G`-nonadjacent to that component.
@isnad1 id=not.3h6v.s6.76e368f929fb from=translated src=- shape=92a4cfca vocab=5f746d70
-/
lemma not_adj_of_mem_other_component {s : Set V}
    {C : (G.induce s).ConnectedComponent} {x y : V}
    (hx : x ∈ s) (hxC : (⟨x, hx⟩ : s) ∉ C.supp)
    (hy : y ∈ componentVerts C) : ¬ G.Adj x y := by
  intro hadj
  obtain ⟨hy', hyC⟩ := (mem_componentVerts (C := C)).1 hy
  have : (G.induce s).Adj ⟨x, hx⟩ ⟨y, hy'⟩ := by simpa [induce_adj] using hadj
  have : (⟨x, hx⟩ : s) ∈ C.supp := (C.mem_supp_congr_adj this).mpr hyC
  exact hxC this

/--
@isnad1 id=ne.3h6v.s6.619385b136ce from=translated src=- shape=178317c6 vocab=ea5b7678
-/
lemma ne_of_mem_other_component {s : Set V}
    {C : (G.induce s).ConnectedComponent} {x y : V}
    (hx : x ∈ s) (hxC : (⟨x, hx⟩ : s) ∉ C.supp)
    (hy : y ∈ componentVerts C) : x ≠ y := by
  intro hxy
  subst hxy
  have : (⟨x, hx⟩ : s) ∈ C.supp := (mem_componentVerts (C := C)).1 hy |>.2
  exact hxC this

/-- An induced `P4` inside one component of `G.induce s`, together with a vertex of
another component, would be an induced `P4 ∪ P1`.
@isnad1 id=iscograp.3h5v.s6.e25ff711303e from=translated src=- shape=6e8fdf5c vocab=a85da724
-/
lemma isCographOn_componentVerts_of_outside_vertex
    (h : NoInducedP4UnionP1 G) {s : Set V}
    (C : (G.induce s).ConnectedComponent) {x : V}
    (hx : x ∈ s) (hxC : (⟨x, hx⟩ : s) ∉ C.supp) :
    IsCographOn G (componentVerts C) := by
  intro a b c d ha hb hc hd hp
  have hxa : x ≠ a := ne_of_mem_other_component hx hxC ha
  have hxb : x ≠ b := ne_of_mem_other_component hx hxC hb
  have hxc : x ≠ c := ne_of_mem_other_component hx hxC hc
  have hxd : x ≠ d := ne_of_mem_other_component hx hxC hd
  have hmeet := h hp hxa hxb hxc hxd
  rcases hmeet with hxa' | hxb' | hxc' | hxd'
  · exact not_adj_of_mem_other_component hx hxC ha hxa'
  · exact not_adj_of_mem_other_component hx hxC hb hxb'
  · exact not_adj_of_mem_other_component hx hxC hc hxc'
  · exact not_adj_of_mem_other_component hx hxC hd hxd'

/-- If `G.induce s` is disconnected, every one of its components induces a cograph.
@isnad1 id=iscograp.2h4v.s5.ace1199cc2a2 from=translated src=- shape=05af2365 vocab=5c8ebf67
-/
lemma isCographOn_componentVerts_of_not_preconnected
    (h : NoInducedP4UnionP1 G) {s : Set V}
    (hdisc : ¬ (G.induce s).Preconnected)
    (C : (G.induce s).ConnectedComponent) :
    IsCographOn G (componentVerts C) := by
  have : ∃ z : s, z ∉ C.supp := by
    by_contra hz
    push Not at hz
    have : (G.induce s).Preconnected := by
      intro u v
      have hu : u ∈ C.supp := hz u
      have hv : v ∈ C.supp := hz v
      exact ConnectedComponent.exact <| by
        rw [ConnectedComponent.mem_supp_iff] at hu hv
        rw [hu, hv]
    exact hdisc this
  obtain ⟨z, hz⟩ := this
  exact isCographOn_componentVerts_of_outside_vertex h C z.2 hz

end Cograph
end Nikoghosyan
