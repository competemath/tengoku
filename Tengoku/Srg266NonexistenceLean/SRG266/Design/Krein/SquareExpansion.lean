/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Design.Krein.FourthTrace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators Matrix

namespace SRG266.QuasiSymmetric.TripleDesign57

variable {P B : Type*} [Fintype P] [DecidableEq P] [Fintype B] [DecidableEq B]
    (D : TripleDesign57 P B)

local notation "V" => KreinVertex (P := P) (B := B)

/--
@isnad1 id=le.0h6v.s5.3fffb9515521 from=translated src=- shape=642c24c6 vocab=f8bae2a4
-/
theorem commonCount_le_neighborCount (T : Finset V) (x y : V) :
    D.commonCount T x y ≤ D.neighborCount T x := by
  apply Finset.card_le_card
  intro z hz
  obtain ⟨hzT,hxz,_⟩ := Finset.mem_filter.mp hz
  exact Finset.mem_filter.mpr ⟨hzT,hxz⟩

/--
@isnad1 id=le.1h7v.s6.7bce5a85e068 from=translated src=- shape=5a018e8b vocab=1312eb55
-/
theorem commonCount_mono {T U : Finset V} (hTU : T ⊆ U) (x y : V) :
    D.commonCount T x y ≤ D.commonCount U x y :=
  Finset.card_le_card (Finset.filter_subset_filter _ hTU)

/--
@isnad1 id=eq.0h6v.s7.d1c625e69876 from=translated src=- shape=97732985 vocab=90623713
-/
theorem commonCount_eq_inter (T : Finset V) (x y : V) :
    D.commonCount T x y =
      ((T.filter fun z => D.kreinGraph.Adj x z) ∩ (T.filter fun z => D.kreinGraph.Adj y z)).card := by
  unfold commonCount
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_inter]
  tauto

/--
@isnad1 id=le.0h6v.s6.1c746e93f514 from=translated src=- shape=3176bc97 vocab=3fe51761
-/
theorem neighbor_pair_count_bound (T : Finset V) (x y : V) :
    D.neighborCount T x + D.neighborCount T y ≤ T.card + D.commonCount T x y := by
  have h := Finset.card_union_add_card_inter
    (T.filter fun z => D.kreinGraph.Adj x z) (T.filter fun z => D.kreinGraph.Adj y z)
  have hb : ((T.filter fun z => D.kreinGraph.Adj x z) ∪
      (T.filter fun z => D.kreinGraph.Adj y z)).card ≤ T.card :=
    Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  rw [← D.commonCount_eq_inter] at h
  change _ + D.commonCount T x y = D.neighborCount T x + D.neighborCount T y at h
  omega

def zeroNeighborUnion (S : Finset V) (x y : V) : Finset V :=
  ((D.bicliqueClass S 0).filter fun z => D.kreinGraph.Adj x z) ∪
    ((D.bicliqueClass S 0).filter fun z => D.kreinGraph.Adj y z)

/--
@isnad1 id=le.7h8v.s7.9b30e5599059 from=translated src=- shape=33b2761f vocab=b5b806b2
-/
theorem two_common_of_square {S : Finset V} {x y f g : V}
    (hx : x ∈ D.bicliqueClass S 2) (hy : y ∈ D.bicliqueClass S 2) (hxy : x ≠ y)
    (hxf : D.kreinGraph.Adj x f) (hxg : D.kreinGraph.Adj x g)
    (hyf : D.kreinGraph.Adj y f) (hyg : D.kreinGraph.Adj y g) :
    2 ≤ D.commonCount (D.bicliqueClass S 2) f g := by
  have hsub : {x,y} ⊆ (D.bicliqueClass S 2).filter
      (fun z => D.kreinGraph.Adj f z ∧ D.kreinGraph.Adj g z) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz
    · subst z
      exact Finset.mem_filter.mpr ⟨hx, (D.kreinGraph.adj_comm x f).mp hxf,
        (D.kreinGraph.adj_comm x g).mp hxg⟩
    · subst z
      exact Finset.mem_filter.mpr ⟨hy, (D.kreinGraph.adj_comm y f).mp hyf,
        (D.kreinGraph.adj_comm y g).mp hyg⟩
  have h := Finset.card_le_card hsub
  simpa [hxy, commonCount] using h

end SRG266.QuasiSymmetric.TripleDesign57
