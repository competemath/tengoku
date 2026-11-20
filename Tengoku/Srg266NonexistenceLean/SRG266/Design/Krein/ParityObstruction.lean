/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Design.Krein.SquareExpansion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators Matrix

namespace SRG266.QuasiSymmetric.TripleDesign57

variable {P B : Type*} [Fintype P] [DecidableEq P] [Fintype B] [DecidableEq B]
    (D : TripleDesign57 P B)

local notation "V" => KreinVertex (P := P) (B := B)

/--
@isnad1 id=le.1h6v.s6.f5e4f422a113 from=translated src=- shape=e87a5322 vocab=74971bbe
-/
theorem neighborCount_mono {T U : Finset V} (hTU : T ⊆ U) (x : V) :
    D.neighborCount T x ≤ D.neighborCount U x :=
  Finset.card_le_card (Finset.filter_subset_filter _ hTU)

/--
@isnad1 id=and.1h5v.s6.2afef8108254 from=translated src=- shape=0bb23813 vocab=059163b9
-/
theorem class_zero_side_counts {S : Finset V} {x : V} (hx : x ∈ D.bicliqueClass S 0) :
    D.neighborCount S x = 0 ∧ D.neighborCount (D.commonTo S) x = 0 := by
  have h := (D.mem_bicliqueClass S 0 x).mp hx |>.2
  rw [D.biclique_neighborCount_split] at h
  omega

end SRG266.QuasiSymmetric.TripleDesign57
