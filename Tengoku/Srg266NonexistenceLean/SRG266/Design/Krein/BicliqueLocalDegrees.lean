/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Design.Krein.BicliqueCensus

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators Matrix

namespace SRG266.QuasiSymmetric.TripleDesign57

variable {P B : Type*} [Fintype P] [DecidableEq P] [Fintype B] [DecidableEq B]
    (D : TripleDesign57 P B)

local notation "V" => KreinVertex (P := P) (B := B)

/--
@isnad1 id=eq.0h5v.s6.d1dfb807b0c7 from=translated src=- shape=10412d9f vocab=90b65c66
-/
theorem biclique_neighborCount_split (S : Finset V) (x : V) :
    D.neighborCount (S ∪ D.commonTo S) x = D.neighborCount S x + D.neighborCount (D.commonTo S) x := by
  simp only [neighborCount, Finset.filter_union]
  exact Finset.card_union_of_disjoint
    ((D.disjoint_commonTo S).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))

def bicliqueOutsideNeighbors (S : Finset V) (x : V) : Finset V :=
  (D.bicliqueOutside S).filter fun y => D.kreinGraph.Adj x y

/--
@isnad1 id=eq.0h6v.s7.d961ebcb8418 from=translated src=- shape=7de0df9c vocab=f182a712
-/
theorem bicliqueOutsideNeighbors_fiber_card (S : Finset V) (x : V) (i : ℕ) :
    ((D.bicliqueOutsideNeighbors S x).filter fun y => D.neighborCount (S ∪ D.commonTo S) y = i).card =
      D.neighborCount (D.bicliqueClass S i) x := by
  unfold bicliqueOutsideNeighbors neighborCount bicliqueClass
  congr 1
  ext y
  simp only [Finset.mem_filter]
  tauto

end SRG266.QuasiSymmetric.TripleDesign57
