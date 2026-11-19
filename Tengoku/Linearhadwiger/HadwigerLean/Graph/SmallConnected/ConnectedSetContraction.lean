import Tengoku.Linearhadwiger.HadwigerLean.Graph.TouchingQuotient
import Tengoku.Linearhadwiger.HadwigerLean.Graph.DensityBasic
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Contracting a connected vertex set

The contracted set becomes `none`; every other vertex remains a singleton.
-/

namespace HadwigerLean

universe u
variable {V : Type u}

abbrev ConnectedSetContractionVertex (H : Set V) :=
  Option {x : V // x ∉ H}

def connectedSetContractionBlock (H : Set V) :
    ConnectedSetContractionVertex H → Set V
  | none => H
  | some x => {x.1}

/--
@isnad1 id=connecte.1h4v.s5.386577284c6c from=translated src=- shape=3d15584f vocab=e89ba191
-/
theorem connectedSetContractionBlock_connected
    (G : SimpleGraph V) (H : Set V)
    (hconn : (G.induce H).Connected)
    (i : ConnectedSetContractionVertex H) :
    (G.induce (connectedSetContractionBlock H i)).Connected := by
  cases i with
  | none => exact hconn
  | some x => simp [connectedSetContractionBlock]

/--
@isnad1 id=pairwise.0h2v.s5.2380563abd31 from=translated src=- shape=11739228 vocab=409c3c4c
-/
theorem connectedSetContractionBlock_disjoint (H : Set V) :
    Pairwise fun i j : ConnectedSetContractionVertex H =>
      Disjoint (connectedSetContractionBlock H i)
        (connectedSetContractionBlock H j) := by
  intro i j hij
  cases i with
  | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some y =>
          apply Set.disjoint_left.mpr
          intro x hx hy
          have hxy : x = y.1 := by simpa [connectedSetContractionBlock] using hy
          exact y.2 (hxy ▸ hx)
  | some x =>
      cases j with
      | none =>
          apply Set.disjoint_left.mpr
          intro z hz hH
          have hzx : z = x.1 := by simpa [connectedSetContractionBlock] using hz
          exact x.2 (hzx ▸ hH)
      | some y =>
          apply Set.disjoint_left.mpr
          intro z hz hz'
          have hzx : z = x.1 := by simpa [connectedSetContractionBlock] using hz
          have hzy : z = y.1 := by simpa [connectedSetContractionBlock] using hz'
          apply hij
          exact congrArg some (Subtype.ext (hzx.symm.trans hzy))

/--
@isnad1 id=ex.0h3v.s4.c1202a58ace2 from=translated src=- shape=c96b7329 vocab=ee0be404
-/
theorem connectedSetContractionBlock_cover (H : Set V) (x : V) :
    ∃ i : ConnectedSetContractionVertex H,
      x ∈ connectedSetContractionBlock H i := by
  by_cases hx : x ∈ H
  · exact ⟨none, hx⟩
  · exact ⟨some ⟨x, hx⟩, by simp [connectedSetContractionBlock]⟩

def connectedSetContractionPartition
    (G : SimpleGraph V) (H : Set V)
    (hconn : (G.induce H).Connected) :
    ConnectedPartition G (ConnectedSetContractionVertex H) where
  block := connectedSetContractionBlock H
  connected := connectedSetContractionBlock_connected G H hconn
  disjoint := connectedSetContractionBlock_disjoint H
  cover := connectedSetContractionBlock_cover H

def connectedSetContractionGraph
    (G : SimpleGraph V) (H : Set V)
    (hconn : (G.induce H).Connected) :
    SimpleGraph (ConnectedSetContractionVertex H) :=
  (connectedSetContractionPartition G H hconn).touchingQuotient

/--
@isnad1 id=isminor.1h3v.s4.d8228d61161f from=translated src=- shape=30ae76ab vocab=e1cf3dbe
-/
theorem connectedSetContraction_isMinor
    (G : SimpleGraph V) (H : Set V)
    (hconn : (G.induce H).Connected) :
    IsMinor (connectedSetContractionGraph G H hconn) G :=
  (connectedSetContractionPartition G H hconn).isMinor

/--
@isnad1 id=iff.1h4v.s6.5cef8bef311a from=translated src=- shape=9855606e vocab=b025b5d5
-/
theorem connectedSetContraction_adj_none_some
    (G : SimpleGraph V) (H : Set V)
    (hconn : (G.induce H).Connected)
    (x : {x : V // x ∉ H}) :
    (connectedSetContractionGraph G H hconn).Adj none (some x) ↔
      ∃ y ∈ H, G.Adj y x.1 := by
  simp [connectedSetContractionGraph, connectedSetContractionPartition,
    ConnectedPartition.touchingQuotient_adj_iff,
    connectedSetContractionBlock]

/--
@isnad1 id=iff.1h5v.s6.ff1651da83e7 from=translated src=- shape=f714cc7e vocab=bec10e51
-/
theorem connectedSetContraction_adj_some_some
    (G : SimpleGraph V) (H : Set V)
    (hconn : (G.induce H).Connected)
    (x y : {x : V // x ∉ H}) :
    (connectedSetContractionGraph G H hconn).Adj (some x) (some y) ↔
      G.Adj x.1 y.1 := by
  constructor
  · intro h
    rcases h.2 with ⟨a, ha, b, hb, hab⟩
    have hax : a = x.1 := by simpa [connectedSetContractionGraph,
      connectedSetContractionPartition, connectedSetContractionBlock] using ha
    have hby : b = y.1 := by simpa [connectedSetContractionGraph,
      connectedSetContractionPartition, connectedSetContractionBlock] using hb
    simpa [hax, hby] using hab
  · intro hxy
    have hne : x ≠ y := by
      intro h
      subst y
      exact G.irrefl hxy
    exact ⟨by simpa using hne,
      x.1, by simp [connectedSetContractionPartition, connectedSetContractionBlock],
      y.1, by simp [connectedSetContractionPartition, connectedSetContractionBlock], hxy⟩

/-- Contracting a finite set removes all but one of its vertices.
@isnad1 id=eq.0h2v.s6.f61e2139b79b from=translated src=- shape=c01b8d19 vocab=a867fda8
-/
theorem connectedSetContraction_card_add
    {V : Type u} [Fintype V] [DecidableEq V]
    (H : Finset V) :
    Fintype.card (ConnectedSetContractionVertex (H : Set V)) + H.card =
      Fintype.card V + 1 := by
  classical
  have houtside : Fintype.card {x : V // x ∉ (H : Set V)} =
      (Hᶜ : Finset V).card := by
    apply Fintype.card_of_subtype
    intro x
    simp
  change Fintype.card (Option {x : V // x ∉ (H : Set V)}) + H.card =
    Fintype.card V + 1
  rw [Fintype.card_option, houtside, Finset.card_compl]
  have hle : H.card ≤ Fintype.card V := Finset.card_le_univ H
  omega

/--
@isnad1 id=le.1h2v.s6.a1c9e624639a from=translated src=- shape=0ed16614 vocab=1c66d0e5
-/
theorem connectedSetContraction_card_le
    {V : Type u} [Fintype V] [DecidableEq V]
    (H : Finset V) (hH : H.Nonempty) :
    Fintype.card (ConnectedSetContractionVertex (H : Set V)) ≤
      Fintype.card V := by
  have h := connectedSetContraction_card_add H
  have hpos : 1 ≤ H.card := Finset.card_pos.mpr hH
  omega
end HadwigerLean
