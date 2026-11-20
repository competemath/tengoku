/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Design.Krein.Companion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators Matrix

namespace SRG266.QuasiSymmetric.TripleDesign57

variable {P B : Type*} [Fintype P] [DecidableEq P] [Fintype B] [DecidableEq B]
    (D : TripleDesign57 P B)

local notation "V" => KreinVertex (P := P) (B := B)

structure CrownParts (L R : Finset V) : Prop where
  left_card : L.card = 6
  right_card : R.card = 6
  disjoint : Disjoint L R
  left_independent : D.IndependentSet L
  right_independent : D.IndependentSet R
  left_degree : ∀ x ∈ L, D.neighborCount R x = 5
  right_degree : ∀ x ∈ R, D.neighborCount L x = 5

def IsCrown (W : Finset V) : Prop := ∃ L R : Finset V, D.CrownParts L R ∧ W = L ∪ R

theorem independentSet_mono {T U : Finset V} (hTU : T ⊆ U) (hI : D.IndependentSet U) :
    D.IndependentSet T := fun x hx y hy hxy => hI x (hTU hx) y (hTU hy) hxy

theorem independent_neighborCount_zero {T : Finset V} (hI : D.IndependentSet T)
    {x : V} (hx : x ∈ T) : D.neighborCount T x = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_of_forall_notMem
  intro y hy
  obtain ⟨hyT,hxy⟩ := Finset.mem_filter.mp hy
  exact hI x hx y hyT (D.kreinGraph.ne_of_adj hxy) hxy

theorem not_adj_of_neighborCount_zero {T : Finset V} {x y : V}
    (hzero : D.neighborCount T x = 0) (hy : y ∈ T) : ¬ D.kreinGraph.Adj x y := by
  intro hxy
  have hp : 0 < D.neighborCount T x := Finset.card_pos.mpr ⟨y,Finset.mem_filter.mpr ⟨hy,hxy⟩⟩
  omega

theorem independentSet_union {T U : Finset V} (hT : D.IndependentSet T)
    (hU : D.IndependentSet U) (hcross : ∀ x ∈ T, ∀ y ∈ U, ¬ D.kreinGraph.Adj x y) :
    D.IndependentSet (T ∪ U) := by
  intro x hx y hy hxy ha
  rcases Finset.mem_union.mp hx with hxT | hxU <;> rcases Finset.mem_union.mp hy with hyT | hyU
  · exact hT x hxT y hyT hxy ha
  · exact hcross x hxT y hyU ha
  · exact hcross y hyT x hxU ((D.kreinGraph.adj_comm x y).mp ha)
  · exact hU x hxU y hyU hxy ha

theorem companions_disjoint {S R : Finset V}
    (hsub : R ∪ D.commonTo R ⊆ D.bicliqueClass S 2) :
    Disjoint (S ∪ D.commonTo S) (R ∪ D.commonTo R) := by
  apply Finset.disjoint_left.mpr
  intro x hxS hxR
  exact ((D.mem_bicliqueClass S 2 x).mp (hsub hxR)).1 hxS

end SRG266.QuasiSymmetric.TripleDesign57
