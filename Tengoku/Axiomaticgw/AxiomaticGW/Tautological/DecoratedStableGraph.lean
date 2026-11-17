/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.Combinatorics.StableGraph
public import Tengoku.Seed.Algebra.BigOperators.Finsupp.Basic
public import Tengoku.Seed.Data.PNat.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite decorated stable graphs

This file gives a universe-small presentation of stable graphs and decorates
their vertices and flags by kappa and psi powers. It is the combinatorial
syntax for tautological strata. A decoration represents the pushforward of
the corresponding monomial along the graph gluing map; no division by the
automorphism group of the graph is built into the definition.
-/

@[expose] public section

namespace AxiomaticGW

open scoped BigOperators

/-- A universe-small stable graph whose vertices and edges have fixed `Fin`
presentations. The existing `StableGraph` remains the representation used by
the abstract CohFT API; this code is the finite syntax used for strata.-/
structure StableGraphCode (S : Type) [Fintype S] where
  /-- Number of vertices.-/
  vertexCount : ℕ
  /-- Number of internal edges.-/
  edgeCount : ℕ
  /-- A connected graph has at least one vertex.-/
  vertexCount_pos : 0 < vertexCount
  /-- Vertex carrying an external leg.-/
  legVertex : S → Fin vertexCount
  /-- Vertex incident to a branch of an internal edge.-/
  endpoint : Fin edgeCount → Fin 2 → Fin vertexCount
  /-- Genus decorating each vertex.-/
  genus : Fin vertexCount → ℕ
  /-- Connectedness via unoriented internal edges.-/
  connected : ∀ v w, Relation.ReflTransGen
    (fun x y ↦ ∃ e, (endpoint e 0 = x ∧ endpoint e 1 = y) ∨
      (endpoint e 1 = x ∧ endpoint e 0 = y)) v w
  /-- Stability at every vertex, with loops counted twice.-/
  stable : ∀ v, 3 ≤ 2 * genus v +
    Fintype.card {s : S // legVertex s = v} +
    Fintype.card {p : Fin edgeCount × Fin 2 // endpoint p.1 p.2 = v}

namespace StableGraphCode

variable {S : Type} [Fintype S]

/-- Forget the fixed finite presentation and obtain the general stable graph
used elsewhere in the project.-/
def toStableGraph (G : StableGraphCode S) : StableGraph S where
  Vertex := Fin G.vertexCount
  Edge := Fin G.edgeCount
  vertexNonempty := ⟨⟨0, G.vertexCount_pos⟩⟩
  legVertex := G.legVertex
  endpoint := G.endpoint
  genus := G.genus
  connected := G.connected
  stable := G.stable

/-- First Betti number of the underlying connected graph.-/
def firstBetti (G : StableGraphCode S) : ℕ :=
  G.edgeCount + 1 - G.vertexCount

/-- Arithmetic genus of a finite stable graph code.-/
def totalGenus (G : StableGraphCode S) : ℕ :=
  (∑ v, G.genus v) + G.firstBetti

/--
@isnad1 id=eq.0h2v.s4.11efcb7dcf8d from=translated src=- shape=3872b343 vocab=596fe879
-/
@[simp]
theorem toStableGraph_firstBetti (G : StableGraphCode S) :
    G.toStableGraph.firstBetti = G.firstBetti := by
  unfold StableGraph.firstBetti firstBetti
  change Fintype.card (Fin G.edgeCount) + 1 - Fintype.card (Fin G.vertexCount) =
    G.edgeCount + 1 - G.vertexCount
  rw [Fintype.card_fin, Fintype.card_fin]

/--
@isnad1 id=eq.0h2v.s4.d565fd187694 from=translated src=- shape=3872b343 vocab=fd45c892
-/
@[simp]
theorem toStableGraph_totalGenus (G : StableGraphCode S) :
    G.toStableGraph.totalGenus = G.totalGenus := by
  change (∑ v, G.genus v) + G.toStableGraph.firstBetti =
    (∑ v, G.genus v) + G.firstBetti
  rw [G.toStableGraph_firstBetti]

/-- Isomorphism of stable graph codes fixing the external labels.-/
structure Iso (G H : StableGraphCode S) where
  /-- Bijection between vertices.-/
  vertexEquiv : Fin G.vertexCount ≃ Fin H.vertexCount
  /-- Bijection between internal edges.-/
  edgeEquiv : Fin G.edgeCount ≃ Fin H.edgeCount
  /-- Bijection between the two branches of each internal edge.-/
  branchEquiv : (e : Fin G.edgeCount) → Fin 2 ≃ Fin 2
  /-- External legs retain their labels.-/
  legVertex_comm : ∀ s, vertexEquiv (G.legVertex s) = H.legVertex s
  /-- Incidence is preserved, allowing the two branches of an edge to be
  exchanged.-/
  endpoint_comm : ∀ e i,
    vertexEquiv (G.endpoint e i) =
      H.endpoint (edgeEquiv e) (branchEquiv e i)
  /-- Vertex genera are preserved.-/
  genus_comm : ∀ v, H.genus (vertexEquiv v) = G.genus v

namespace Iso

/-- Identity graph-code isomorphism.-/
def refl (G : StableGraphCode S) : Iso G G where
  vertexEquiv := Equiv.refl _
  edgeEquiv := Equiv.refl _
  branchEquiv := fun _ ↦ Equiv.refl _
  legVertex_comm := by intros; rfl
  endpoint_comm := by intros; rfl
  genus_comm := by intros; rfl

/-- Inverse graph-code isomorphism.-/
def symm {G H : StableGraphCode S} (e : Iso G H) : Iso H G where
  vertexEquiv := e.vertexEquiv.symm
  edgeEquiv := e.edgeEquiv.symm
  branchEquiv := fun edge ↦
    (e.branchEquiv (e.edgeEquiv.symm edge)).symm
  legVertex_comm := by
    intro s
    apply e.vertexEquiv.injective
    simp only [Equiv.apply_symm_apply, e.legVertex_comm]
  endpoint_comm := by
    intro edge i
    apply e.vertexEquiv.injective
    simpa only [Equiv.apply_symm_apply, Equiv.symm_apply_apply] using
      (e.endpoint_comm (e.edgeEquiv.symm edge)
        ((e.branchEquiv (e.edgeEquiv.symm edge)).symm i)).symm
  genus_comm := by
    intro v
    simpa only [Equiv.apply_symm_apply] using
      (e.genus_comm (e.vertexEquiv.symm v)).symm

/-- Composite graph-code isomorphism.-/
def trans {G H K : StableGraphCode S} (e : Iso G H) (f : Iso H K) : Iso G K where
  vertexEquiv := e.vertexEquiv.trans f.vertexEquiv
  edgeEquiv := e.edgeEquiv.trans f.edgeEquiv
  branchEquiv := fun edge ↦
    (e.branchEquiv edge).trans (f.branchEquiv (e.edgeEquiv edge))
  legVertex_comm := by
    intro s
    simp only [Equiv.trans_apply, e.legVertex_comm, f.legVertex_comm]
  endpoint_comm := by
    intro edge i
    simp only [Equiv.trans_apply, e.endpoint_comm, f.endpoint_comm]
  genus_comm := by
    intro v
    simp only [Equiv.trans_apply, f.genus_comm, e.genus_comm]

/-- Isomorphic graph codes have the same number of vertices.
@isnad1 id=eq.0h4v.s4.752f1a20b90a from=translated src=- shape=06022485 vocab=4d11e4d8
-/
theorem vertexCount_eq {G H : StableGraphCode S} (e : Iso G H) :
    G.vertexCount = H.vertexCount := by
  simpa only [Fintype.card_fin] using Fintype.card_congr e.vertexEquiv

/-- Isomorphic graph codes have the same number of edges.
@isnad1 id=eq.0h4v.s4.4b57b1f08cd1 from=translated src=- shape=06022485 vocab=99f66e61
-/
theorem edgeCount_eq {G H : StableGraphCode S} (e : Iso G H) :
    G.edgeCount = H.edgeCount := by
  simpa only [Fintype.card_fin] using Fintype.card_congr e.edgeEquiv

/-- Isomorphic graph codes have the same sum of vertex genera.
@isnad1 id=eq.0h4v.s6.5e1db6133cd6 from=translated src=- shape=b3ddaef6 vocab=6080e209
-/
theorem genus_sum_eq {G H : StableGraphCode S} (e : Iso G H) :
    (∑ v, G.genus v) = ∑ v, H.genus v := by
  apply Fintype.sum_equiv e.vertexEquiv
  intro v
  exact (e.genus_comm v).symm

/-- Isomorphic graph codes have the same first Betti number.
@isnad1 id=eq.0h4v.s4.7f656e131fb5 from=translated src=- shape=06022485 vocab=8252c8d0
-/
theorem firstBetti_eq {G H : StableGraphCode S} (e : Iso G H) :
    G.firstBetti = H.firstBetti := by
  unfold StableGraphCode.firstBetti
  rw [e.edgeCount_eq, e.vertexCount_eq]

/-- Isomorphic graph codes have the same arithmetic genus.
@isnad1 id=eq.0h4v.s4.d302654227bb from=translated src=- shape=06022485 vocab=ace0328e
-/
theorem totalGenus_eq {G H : StableGraphCode S} (e : Iso G H) :
    G.totalGenus = H.totalGenus := by
  unfold StableGraphCode.totalGenus
  rw [e.genus_sum_eq, e.firstBetti_eq]

end Iso

/-- Two graph codes are isomorphic when a label-preserving isomorphism
exists.-/
def Isomorphic (G H : StableGraphCode S) : Prop := Nonempty (Iso G H)

/--
@isnad1 id=isomorph.0h2v.s3.072df5d36805 from=translated src=- shape=53c84fe7 vocab=18b0e68c
-/
theorem isomorphic_refl (G : StableGraphCode S) : Isomorphic G G :=
  ⟨Iso.refl G⟩

/--
@isnad1 id=isomorph.1h3v.s4.e09f2c26bddf from=translated src=- shape=34baef30 vocab=18b0e68c
-/
theorem isomorphic_symm {G H : StableGraphCode S} :
    Isomorphic G H → Isomorphic H G := by
  rintro ⟨e⟩
  exact ⟨e.symm⟩

/--
@isnad1 id=isomorph.2h4v.s5.cb40d3c86a10 from=translated src=- shape=46b34526 vocab=18b0e68c
-/
theorem isomorphic_trans {G H K : StableGraphCode S} :
    Isomorphic G H → Isomorphic H K → Isomorphic G K := by
  rintro ⟨e⟩ ⟨f⟩
  exact ⟨e.trans f⟩

end StableGraphCode

/-- A stable graph decorated by positive-index kappa powers at vertices and
psi powers at all external and internal flags. The omission of `kappa_0`
uses its scalar reduction and keeps fixed-degree syntax finite.-/
structure DecoratedStableGraph (S : Type) [Fintype S] where
  /-- Underlying stable graph code.-/
  graph : StableGraphCode S
  /-- Multiplicity of each positive-index kappa class at each vertex.-/
  kappaPower : Fin graph.vertexCount → ℕ+ →₀ ℕ
  /-- Psi exponent at each external marking.-/
  legPsiPower : S → ℕ
  /-- Psi exponent at each internal half-edge.-/
  halfEdgePsiPower : Fin graph.edgeCount → Fin 2 → ℕ

namespace DecoratedStableGraph

variable {S : Type} [Fintype S]

/-- Codimension contributed by the kappa decorations.-/
def kappaCodimension (G : DecoratedStableGraph S) : ℕ :=
  ∑ v, (G.kappaPower v).sum fun i power ↦ (i : ℕ) * power

/-- Codimension contributed by psi decorations on external markings.-/
def legPsiCodimension (G : DecoratedStableGraph S) : ℕ :=
  ∑ s, G.legPsiPower s

/-- Codimension contributed by psi decorations on internal half-edges.-/
def halfEdgePsiCodimension (G : DecoratedStableGraph S) : ℕ :=
  ∑ e, ∑ i, G.halfEdgePsiPower e i

/-- Total codimension of a decorated stratum. Every internal edge contributes
one in addition to the kappa and psi decorations.-/
def codimension (G : DecoratedStableGraph S) : ℕ :=
  G.graph.edgeCount + G.kappaCodimension + G.legPsiCodimension +
    G.halfEdgePsiCodimension

/-- Isomorphism of decorated stable graphs. Decorations are transported by
the underlying vertex and edge equivalences, while external labels remain
fixed.-/
structure Iso (G H : DecoratedStableGraph S) where
  /-- Isomorphism of the underlying stable graph codes.-/
  graphIso : StableGraphCode.Iso G.graph H.graph
  /-- Kappa decorations are preserved at corresponding vertices.-/
  kappaPower_comm : ∀ v i,
    H.kappaPower (graphIso.vertexEquiv v) i = G.kappaPower v i
  /-- Psi decorations at external labels are preserved.-/
  legPsiPower_comm : ∀ s, H.legPsiPower s = G.legPsiPower s
  /-- Psi decorations at internal flags are preserved.-/
  halfEdgePsiPower_comm : ∀ e i,
    H.halfEdgePsiPower (graphIso.edgeEquiv e) (graphIso.branchEquiv e i) =
      G.halfEdgePsiPower e i

namespace Iso

/-- Identity decorated-graph isomorphism.-/
def refl (G : DecoratedStableGraph S) : Iso G G where
  graphIso := StableGraphCode.Iso.refl G.graph
  kappaPower_comm := by intros; rfl
  legPsiPower_comm := by intros; rfl
  halfEdgePsiPower_comm := by intros; rfl

/-- Inverse decorated-graph isomorphism.-/
def symm {G H : DecoratedStableGraph S} (e : Iso G H) : Iso H G where
  graphIso := e.graphIso.symm
  kappaPower_comm := by
    intro v i
    change G.kappaPower (e.graphIso.vertexEquiv.symm v) i = H.kappaPower v i
    simpa only [Equiv.apply_symm_apply] using
      (e.kappaPower_comm (e.graphIso.vertexEquiv.symm v) i).symm
  legPsiPower_comm := by
    intro s
    exact (e.legPsiPower_comm s).symm
  halfEdgePsiPower_comm := by
    intro edge i
    change G.halfEdgePsiPower (e.graphIso.edgeEquiv.symm edge)
        ((e.graphIso.branchEquiv
          (e.graphIso.edgeEquiv.symm edge)).symm i) =
      H.halfEdgePsiPower edge i
    simpa only [Equiv.apply_symm_apply, Equiv.symm_apply_apply] using
      (e.halfEdgePsiPower_comm
        (e.graphIso.edgeEquiv.symm edge)
        ((e.graphIso.branchEquiv
          (e.graphIso.edgeEquiv.symm edge)).symm i)).symm

/-- Composite decorated-graph isomorphism.-/
def trans {G H K : DecoratedStableGraph S} (e : Iso G H) (f : Iso H K) : Iso G K where
  graphIso := e.graphIso.trans f.graphIso
  kappaPower_comm := by
    intro v i
    simp only [StableGraphCode.Iso.trans, Equiv.trans_apply,
      f.kappaPower_comm, e.kappaPower_comm]
  legPsiPower_comm := by
    intro s
    exact (f.legPsiPower_comm s).trans (e.legPsiPower_comm s)
  halfEdgePsiPower_comm := by
    intro edge i
    simp only [StableGraphCode.Iso.trans, Equiv.trans_apply,
      f.halfEdgePsiPower_comm, e.halfEdgePsiPower_comm]

/-- Isomorphic decorations have equal kappa codimension.
@isnad1 id=eq.0h4v.s4.5e1da93fe172 from=translated src=- shape=06022485 vocab=d52684b0
-/
theorem kappaCodimension_eq {G H : DecoratedStableGraph S} (e : Iso G H) :
    G.kappaCodimension = H.kappaCodimension := by
  unfold DecoratedStableGraph.kappaCodimension
  apply Fintype.sum_equiv e.graphIso.vertexEquiv
  intro v
  have hk : H.kappaPower (e.graphIso.vertexEquiv v) = G.kappaPower v := by
    ext i
    exact e.kappaPower_comm v i
  rw [hk]

/-- Isomorphic decorations have equal external psi codimension.
@isnad1 id=eq.0h4v.s4.b597b208a241 from=translated src=- shape=06022485 vocab=d4952079
-/
theorem legPsiCodimension_eq {G H : DecoratedStableGraph S} (e : Iso G H) :
    G.legPsiCodimension = H.legPsiCodimension := by
  unfold DecoratedStableGraph.legPsiCodimension
  apply Fintype.sum_congr
  intro s
  exact (e.legPsiPower_comm s).symm

/-- Isomorphic decorations have equal internal psi codimension.
@isnad1 id=eq.0h4v.s4.eefaed4807e9 from=translated src=- shape=06022485 vocab=05d3046e
-/
theorem halfEdgePsiCodimension_eq {G H : DecoratedStableGraph S} (e : Iso G H) :
    G.halfEdgePsiCodimension = H.halfEdgePsiCodimension := by
  unfold DecoratedStableGraph.halfEdgePsiCodimension
  apply Fintype.sum_equiv e.graphIso.edgeEquiv
  intro edge
  apply Fintype.sum_equiv (e.graphIso.branchEquiv edge)
  intro i
  exact (e.halfEdgePsiPower_comm edge i).symm

/-- Codimension is independent of the finite graph presentation.
@isnad1 id=eq.0h4v.s4.5e14502487ee from=translated src=- shape=06022485 vocab=4594e6a6
-/
theorem codimension_eq {G H : DecoratedStableGraph S} (e : Iso G H) :
    G.codimension = H.codimension := by
  unfold DecoratedStableGraph.codimension
  rw [e.graphIso.edgeCount_eq, e.kappaCodimension_eq,
    e.legPsiCodimension_eq, e.halfEdgePsiCodimension_eq]

end Iso

/-- Isomorphism relation on decorated stable graphs.-/
def Isomorphic (G H : DecoratedStableGraph S) : Prop := Nonempty (Iso G H)

/--
@isnad1 id=isomorph.0h2v.s3.c60246dfbf2e from=translated src=- shape=53c84fe7 vocab=7b96f7e8
-/
theorem isomorphic_refl (G : DecoratedStableGraph S) : Isomorphic G G :=
  ⟨Iso.refl G⟩

/--
@isnad1 id=isomorph.1h3v.s4.b6bca5c8116f from=translated src=- shape=34baef30 vocab=7b96f7e8
-/
theorem isomorphic_symm {G H : DecoratedStableGraph S} :
    Isomorphic G H → Isomorphic H G := by
  rintro ⟨e⟩
  exact ⟨e.symm⟩

/--
@isnad1 id=isomorph.2h4v.s5.ca2e401f670a from=translated src=- shape=46b34526 vocab=7b96f7e8
-/
theorem isomorphic_trans {G H K : DecoratedStableGraph S} :
    Isomorphic G H → Isomorphic H K → Isomorphic G K := by
  rintro ⟨e⟩ ⟨f⟩
  exact ⟨e.trans f⟩

end DecoratedStableGraph

/-- A decorated graph presentation of fixed arithmetic genus.-/
abbrev DecoratedStratumPresentation (g : ℕ) (S : Type) [Fintype S] :=
  {G : DecoratedStableGraph S // G.graph.totalGenus = g}

/-- Isomorphism relation on fixed-genus decorated graph presentations.-/
def decoratedStratumSetoid (g : ℕ) (S : Type) [Fintype S] :
    Setoid (DecoratedStratumPresentation g S) where
  r G H := DecoratedStableGraph.Isomorphic G.1 H.1
  iseqv := {
    refl := fun G ↦ DecoratedStableGraph.isomorphic_refl G.1
    symm := DecoratedStableGraph.isomorphic_symm
    trans := DecoratedStableGraph.isomorphic_trans }

/-- Isomorphism class of a decorated stable graph of genus `g` with external
labels `S`. This is a basis element of the formal strata module.-/
def TautologicalStratum (g : ℕ) (S : Type) [Fintype S] :=
  Quotient (decoratedStratumSetoid g S)

namespace TautologicalStratum

variable {g : ℕ} {S : Type} [Fintype S]

/-- Construct a stratum class from one finite decorated presentation.-/
def mk (G : DecoratedStableGraph S) (hG : G.graph.totalGenus = g) :
    TautologicalStratum g S :=
  Quotient.mk _ ⟨G, hG⟩

/-- Codimension of a tautological stratum.-/
def codimension (x : TautologicalStratum g S) : ℕ :=
  Quotient.liftOn x (fun G ↦ G.1.codimension) fun G H h ↦ by
    rcases h with ⟨e⟩
    exact e.codimension_eq

/--
@isnad1 id=eq.1h3v.s5.2842ed90b167 from=translated src=- shape=e4e6de22 vocab=983fa4a7
-/
@[simp]
theorem codimension_mk (G : DecoratedStableGraph S)
    (hG : G.graph.totalGenus = g) :
    codimension (mk G hG) = G.codimension := rfl

/-- Isomorphic presentations define the same tautological stratum.
@isnad1 id=eq.3h4v.s5.aaa0738d63f6 from=translated src=- shape=1e8df62d vocab=26eafdc8
-/
theorem mk_eq_mk {G H : DecoratedStableGraph S}
    (hG : G.graph.totalGenus = g) (hH : H.graph.totalGenus = g)
    (e : DecoratedStableGraph.Isomorphic G H) :
    mk G hG = mk H hH := by
  exact Quotient.sound e

end TautologicalStratum

end AxiomaticGW
