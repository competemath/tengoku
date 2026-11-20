/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Design.Krein.BicliqueLocalDegrees

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators Matrix

namespace SRG266.QuasiSymmetric.TripleDesign57

variable {P B : Type*} [Fintype P] [DecidableEq P] [Fintype B] [DecidableEq B]
    (D : TripleDesign57 P B)

local notation "V" => KreinVertex (P := P) (B := B)

def commonCount (T : Finset V) (x y : V) : ℕ :=
  (T.filter fun w => D.kreinGraph.Adj x w ∧ D.kreinGraph.Adj y w).card

/--
@isnad1 id=eq.0h5v.s5.b90b83977847 from=translated src=- shape=dfd95b18 vocab=78707bb4
-/
theorem commonCount_self (T : Finset V) (x : V) :
    D.commonCount T x x = D.neighborCount T x := by simp [commonCount, neighborCount]

/--
@isnad1 id=iff.0h6v.s7.db8eb17b8318 from=translated src=- shape=25bdf1c3 vocab=fb99db1b
-/
@[simp] theorem mem_bicliqueClass (S : Finset V) (i : ℕ) (x : V) :
    x ∈ D.bicliqueClass S i ↔ x ∉ S ∪ D.commonTo S ∧
      D.neighborCount (S ∪ D.commonTo S) x = i := by
  simp [bicliqueClass]

def bicliqueCubicLeft (S : Finset V) : Finset V :=
  (S ∪ D.commonTo S) ∪ D.bicliqueClass S 0

/--
@isnad1 id=disjoint.0h5v.s6.77dce4ccff0d from=translated src=- shape=ce510d9c vocab=6309a54e
-/
theorem disjoint_biclique_class (S : Finset V) (i : ℕ) :
    Disjoint (S ∪ D.commonTo S) (D.bicliqueClass S i) := by
  apply Finset.disjoint_left.mpr
  intro x hx hi
  exact ((D.mem_bicliqueClass S i x).mp hi).1 hx

/--
@isnad1 id=eq.1h7v.s7.dc6c5b896f23 from=translated src=- shape=5899df29 vocab=5cb00819
-/
theorem commonCount_union (T U : Finset V) (hd : Disjoint T U) (x y : V) :
    D.commonCount (T ∪ U) x y = D.commonCount T x y + D.commonCount U x y := by
  simp only [commonCount, Finset.filter_union]
  exact Finset.card_union_of_disjoint
    (hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))

end SRG266.QuasiSymmetric.TripleDesign57
