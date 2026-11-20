/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Design.Krein.CommonTrace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators Matrix

namespace SRG266.QuasiSymmetric.TripleDesign57

variable {P B : Type*} [Fintype P] [DecidableEq P] [Fintype B] [DecidableEq B]
    (D : TripleDesign57 P B)

local notation "V" => KreinVertex (P := P) (B := B)

/--
@isnad1 id=eq.1h6v.s7.070267553622 from=translated src=- shape=f08815db vocab=0382bea0
-/
theorem neighborCount_union (T U : Finset V) (hd : Disjoint T U) (x : V) :
    D.neighborCount (T ∪ U) x = D.neighborCount T x + D.neighborCount U x := by
  simp only [neighborCount, Finset.filter_union]
  exact Finset.card_union_of_disjoint
    (hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))

def setAdjMatrix (T : Finset V) : Matrix T T ℤ := fun x y => D.kreinMatrix x y

def crossAdjMatrix (T U : Finset V) : Matrix T U ℤ := fun x y => D.kreinMatrix x y

end SRG266.QuasiSymmetric.TripleDesign57
