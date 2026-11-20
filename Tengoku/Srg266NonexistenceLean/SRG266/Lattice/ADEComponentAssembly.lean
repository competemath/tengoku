/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.ADEBlockCoordinates
import Tengoku.Seed.Combinatorics.SimpleGraph.Connectivity.Finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266
namespace Lattice

open Function Set SimpleGraph

variable {V : Type*}

section ComponentBlocks

variable (G : SimpleGraph V)
variable (typeOf : G.ConnectedComponent → ADEType)
variable (coord : ∀ c : G.ConnectedComponent, Fin (typeOf c).rank ≃ c)

def componentBlockToVertex : (cs : List G.ConnectedComponent) →
    ADEBlockIndex (cs.map typeOf) → V
  | [], i => nomatch i
  | c :: _, Sum.inl i => (coord c i).1
  | _ :: cs, Sum.inr i => componentBlockToVertex cs i

/--
@isnad1 id=mem.0h6v.s6.a43b9deec339 from=translated src=- shape=e81d8ace vocab=9b6c8e08
-/
theorem connectedComponentMk_componentBlockToVertex :
    ∀ (cs : List G.ConnectedComponent) (i : ADEBlockIndex (cs.map typeOf)),
      G.connectedComponentMk (componentBlockToVertex G typeOf coord cs i) ∈ cs
  | [], i => nomatch i
  | c :: cs, Sum.inl i => by
      simp only [componentBlockToVertex, List.mem_cons]
      left
      exact (ConnectedComponent.mem_supp_iff c (coord c i).1).mp (coord c i).2
  | c :: cs, Sum.inr i => by
      simp only [componentBlockToVertex, List.mem_cons]
      exact Or.inr (connectedComponentMk_componentBlockToVertex cs i)

/--
@isnad1 id=injectiv.1h5v.s6.6d0316f5b9f2 from=translated src=- shape=c8e37552 vocab=7ac8e289
-/
theorem componentBlockToVertex_injective :
    ∀ {cs : List G.ConnectedComponent}, cs.Nodup →
      Function.Injective (componentBlockToVertex G typeOf coord cs)
  | [], _, i, _ => nomatch i
  | c :: cs, hnodup, i, j => by
      have hcnot : c ∉ cs := (List.nodup_cons.mp hnodup).1
      have htail : cs.Nodup := (List.nodup_cons.mp hnodup).2
      cases i with
      | inl i =>
          cases j with
          | inl j =>
              intro hij
              have hcoord : coord c i = coord c j := Subtype.ext hij
              have : i = j := (coord c).injective hcoord
              subst j
              rfl
          | inr j =>
              intro hij
              have hcomp := congrArg G.connectedComponentMk hij
              have hleft : G.connectedComponentMk (coord c i).1 = c :=
                (ConnectedComponent.mem_supp_iff c (coord c i).1).mp (coord c i).2
              have hright : G.connectedComponentMk
                  (componentBlockToVertex G typeOf coord cs j) ∈ cs :=
                connectedComponentMk_componentBlockToVertex G typeOf coord cs j
              exact (hcnot (hleft ▸ hcomp ▸ hright)).elim
      | inr i =>
          cases j with
          | inl j =>
              intro hij
              have hcomp := congrArg G.connectedComponentMk hij
              have hleft : G.connectedComponentMk
                  (componentBlockToVertex G typeOf coord cs i) ∈ cs :=
                connectedComponentMk_componentBlockToVertex G typeOf coord cs i
              have hright : G.connectedComponentMk (coord c j).1 = c :=
                (ConnectedComponent.mem_supp_iff c (coord c j).1).mp (coord c j).2
              exact (hcnot (hright ▸ hcomp.symm ▸ hleft)).elim
          | inr j =>
              intro hij
              have : i = j := componentBlockToVertex_injective htail hij
              subst j
              rfl

/--
@isnad1 id=ex.1h6v.s6.1f407cc0a781 from=translated src=- shape=c6f19f40 vocab=9b6c8e08
-/
theorem exists_componentBlockToVertex_eq :
    ∀ (cs : List G.ConnectedComponent) (v : V),
      G.connectedComponentMk v ∈ cs →
        ∃ i : ADEBlockIndex (cs.map typeOf),
          componentBlockToVertex G typeOf coord cs i = v
  | [], _, h => by simp at h
  | c :: cs, v, h => by
      rw [List.mem_cons] at h
      rcases h with h | h
      · have hv : v ∈ c := (ConnectedComponent.mem_supp_iff c v).mpr h
        obtain ⟨i, hi⟩ := (coord c).surjective ⟨v, hv⟩
        exact ⟨Sum.inl i, congrArg Subtype.val hi⟩
      · obtain ⟨i, hi⟩ := exists_componentBlockToVertex_eq cs v h
        exact ⟨Sum.inr i, hi⟩

/--
@isnad1 id=surjecti.1h5v.s6.bd9cf846edac from=translated src=- shape=6741f48d vocab=397a9900
-/
theorem componentBlockToVertex_surjective
    (cs : List G.ConnectedComponent)
    (hcover : ∀ c : G.ConnectedComponent, c ∈ cs) :
    Function.Surjective (componentBlockToVertex G typeOf coord cs) := by
  intro v
  exact exists_componentBlockToVertex_eq G typeOf coord cs v
    (hcover (G.connectedComponentMk v))

noncomputable def componentBlockEquiv
    (cs : List G.ConnectedComponent) (hnodup : cs.Nodup)
    (hcover : ∀ c : G.ConnectedComponent, c ∈ cs) :
    ADEBlockIndex (cs.map typeOf) ≃ V :=
  Equiv.ofBijective (componentBlockToVertex G typeOf coord cs)
    ⟨componentBlockToVertex_injective G typeOf coord hnodup,
      componentBlockToVertex_surjective G typeOf coord cs hcover⟩

/--
@isnad1 id=eq.2h6v.s7.89f3012ca3c6 from=translated src=- shape=c4e2beab vocab=2d4a4e7d
-/
@[simp]
theorem componentBlockEquiv_apply
    (cs : List G.ConnectedComponent) (hnodup : cs.Nodup)
    (hcover : ∀ c : G.ConnectedComponent, c ∈ cs)
    (i : ADEBlockIndex (cs.map typeOf)) :
    componentBlockEquiv G typeOf coord cs hnodup hcover i =
      componentBlockToVertex G typeOf coord cs i :=
  rfl

/--
@isnad1 id=eq.0h5v.s6.ba5f9ad5908a from=translated src=- shape=27bc226a vocab=8acd24c7
-/
theorem graphCartanMatrix_component
    (c : G.ConnectedComponent) (u v : c) :
    graphCartanMatrix G u.1 v.1 = graphCartanMatrix c.toSimpleGraph u v := by
  classical
  by_cases huv : u = v
  · subst v
    rw [graphCartanMatrix_apply_same, graphCartanMatrix_apply_same]
  · have huvval : u.1 ≠ v.1 := fun h => huv (Subtype.ext h)
    by_cases hadj : G.Adj u.1 v.1
    · have hcadj : c.toSimpleGraph.Adj u v :=
        (ConnectedComponent.toSimpleGraph_adj c u.2 v.2).mpr hadj
      rw [graphCartanMatrix_apply_of_adj hadj,
        graphCartanMatrix_apply_of_adj hcadj]
    · have hcnot : ¬c.toSimpleGraph.Adj u v := fun h =>
        hadj ((ConnectedComponent.toSimpleGraph_adj c u.2 v.2).mp h)
      rw [graphCartanMatrix_apply_of_not_adj huvval hadj,
        graphCartanMatrix_apply_of_not_adj huv hcnot]

/--
@isnad1 id=eq.1h4v.s5.6ce0a9c5a641 from=translated src=- shape=e2709b81 vocab=2511af02
-/
theorem graphCartanMatrix_eq_zero_of_components_ne
    {u v : V} (huv : G.connectedComponentMk u ≠ G.connectedComponentMk v) :
    graphCartanMatrix G u v = 0 := by
  apply graphCartanMatrix_apply_of_not_adj
  · intro h
    exact huv (congrArg G.connectedComponentMk h)
  · intro h
    exact huv (ConnectedComponent.connectedComponentMk_eq_of_adj h)

/--
@isnad1 id=eq.2h7v.s8.83941233351a from=translated src=- shape=3deb6770 vocab=5a6f635b
-/
theorem graphCartanMatrix_componentBlock :
    ∀ (cs : List G.ConnectedComponent), cs.Nodup →
      (∀ c i j, graphCartanMatrix c.toSimpleGraph (coord c i) (coord c j) =
        (typeOf c).gram i j) →
      ∀ i j : ADEBlockIndex (cs.map typeOf),
        graphCartanMatrix G
            (componentBlockToVertex G typeOf coord cs i)
            (componentBlockToVertex G typeOf coord cs j) =
          adeBlockPairing (cs.map typeOf) i j
  | [], _, _, i, _ => nomatch i
  | c :: cs, hnodup, hgram, i, j => by
      have hcnot : c ∉ cs := (List.nodup_cons.mp hnodup).1
      have htail : cs.Nodup := (List.nodup_cons.mp hnodup).2
      cases i with
      | inl i =>
          cases j with
          | inl j =>
              change graphCartanMatrix G (coord c i).1 (coord c j).1 = _
              rw [graphCartanMatrix_component G c (coord c i) (coord c j), hgram]
              rfl
          | inr j =>
              change graphCartanMatrix G (coord c i).1
                (componentBlockToVertex G typeOf coord cs j) = 0
              apply graphCartanMatrix_eq_zero_of_components_ne G
              have hleft : G.connectedComponentMk (coord c i).1 = c :=
                (ConnectedComponent.mem_supp_iff c (coord c i).1).mp (coord c i).2
              have hright : G.connectedComponentMk
                  (componentBlockToVertex G typeOf coord cs j) ∈ cs :=
                connectedComponentMk_componentBlockToVertex G typeOf coord cs j
              intro heq
              exact hcnot (hleft ▸ heq ▸ hright)
      | inr i =>
          cases j with
          | inl j =>
              change graphCartanMatrix G
                (componentBlockToVertex G typeOf coord cs i) (coord c j).1 = 0
              apply graphCartanMatrix_eq_zero_of_components_ne G
              have hleft : G.connectedComponentMk
                  (componentBlockToVertex G typeOf coord cs i) ∈ cs :=
                connectedComponentMk_componentBlockToVertex G typeOf coord cs i
              have hright : G.connectedComponentMk (coord c j).1 = c :=
                (ConnectedComponent.mem_supp_iff c (coord c j).1).mp (coord c j).2
              intro heq
              exact hcnot (hright ▸ heq.symm ▸ hleft)
          | inr j =>
              exact graphCartanMatrix_componentBlock cs htail hgram i j

end ComponentBlocks

section PositiveGraph

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V)

noncomputable instance connectedComponentVertexFintype
    (c : G.ConnectedComponent) : Fintype c :=
  Fintype.ofFinite c

end PositiveGraph

def ADECoordinates [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ ts : List ADEType, (∀ t ∈ ts, t.IsRegular) ∧
    ADEType.rankSum ts = Fintype.card V ∧
    ∃ coord : Fin (ADEType.rankSum ts) ≃ V, ∀ i j,
      graphCartanMatrix G (coord i) (coord j) = (adeGram ts).2 i j

end Lattice
end SRG266
