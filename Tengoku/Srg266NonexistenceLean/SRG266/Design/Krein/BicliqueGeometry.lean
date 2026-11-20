/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Design.Krein.TripleMoments

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.QuasiSymmetric.TripleDesign57

variable {P B : Type*} [Fintype P] [DecidableEq P] [Fintype B] [DecidableEq B]
    (D : TripleDesign57 P B)

local notation "V" => KreinVertex (P := P) (B := B)

def IndependentSet (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ D.kreinGraph.Adj x y

def commonTo (S : Finset V) : Finset V :=
  Finset.univ.filter fun w => ∀ x ∈ S, D.kreinGraph.Adj x w

/--
@isnad1 id=iff.0h5v.s6.ab413a85b2c2 from=translated src=- shape=8fc18b1a vocab=e5099783
-/
@[simp] theorem mem_commonTo (S : Finset V) (w : V) :
    w ∈ D.commonTo S ↔ ∀ x ∈ S, D.kreinGraph.Adj x w := by simp [commonTo]

/--
@isnad1 id=disjoint.0h4v.s5.eec6718a8927 from=translated src=- shape=13958a74 vocab=98720d67
-/
theorem disjoint_commonTo (S : Finset V) : Disjoint S (D.commonTo S) := by
  apply Finset.disjoint_left.mpr
  intro x hx hxC
  exact D.kreinGraph.irrefl ((D.mem_commonTo S x).mp hxC x hx)

/--
@isnad1 id=le.2h5v.s6.885df144d518 from=translated src=- shape=8399b58c vocab=c8f134de
-/
theorem neighbor_trace_le_two {S : Finset V} (hcard : S.card = 3) {x : V}
    (hx : x ∉ D.commonTo S) : (S.filter fun y => D.kreinGraph.Adj x y).card ≤ 2 := by
  by_contra hgt
  have heq : S.filter (fun y => D.kreinGraph.Adj x y) = S :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
  apply hx
  apply (D.mem_commonTo S x).mpr
  intro y hy
  have hmem : y ∈ S.filter fun y => D.kreinGraph.Adj x y := heq.symm ▸ hy
  exact (D.kreinGraph.adj_comm x y).mp (Finset.mem_filter.mp hmem).2

end SRG266.QuasiSymmetric.TripleDesign57
