/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Design.Krein.CrownMatching

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators Matrix

namespace SRG266.QuasiSymmetric.TripleDesign57

variable {P B : Type*} [Fintype P] [DecidableEq P] [Fintype B] [DecidableEq B]
    (D : TripleDesign57 P B)

local notation "V" => KreinVertex (P := P) (B := B)

/--
@isnad1 id=or.4h6v.s7.9d0967f06eb2 from=translated src=- shape=62c695d3 vocab=d2b6a48b
-/
theorem crown_independent_triple_one_part {L R T : Finset V} (h : D.CrownParts L R)
    (hT : T.card = 3) (hTI : D.IndependentSet T) (hsub : T ⊆ L ∪ R) : T ⊆ L ∨ T ⊆ R := by
  by_cases hTL : T ⊆ L
  · exact Or.inl hTL
  · by_cases hTR : T ⊆ R
    · exact Or.inr hTR
    · obtain ⟨x,hxT,hxR⟩ := Finset.not_subset.mp hTR
      obtain ⟨y,hyT,hyL⟩ := Finset.not_subset.mp hTL
      have hxL : x ∈ L := (Finset.mem_union.mp (hsub hxT)).resolve_right hxR
      have hyR : y ∈ R := (Finset.mem_union.mp (hsub hyT)).resolve_left hyL
      have hLsub : T ∩ L ⊆ L.filter (fun z => ¬ D.kreinGraph.Adj y z) := by
        intro z hz
        obtain ⟨hzT,hzL⟩ := Finset.mem_inter.mp hz
        exact Finset.mem_filter.mpr ⟨hzL,fun ha => hTI y hyT z hzT (D.kreinGraph.ne_of_adj ha) ha⟩
      have hRsub : T ∩ R ⊆ R.filter (fun z => ¬ D.kreinGraph.Adj x z) := by
        intro z hz
        obtain ⟨hzT,hzR⟩ := Finset.mem_inter.mp hz
        exact Finset.mem_filter.mpr ⟨hzR,fun ha => hTI x hxT z hzT (D.kreinGraph.ne_of_adj ha) ha⟩
      have hLc := Finset.card_le_card hLsub
      have hRc := Finset.card_le_card hRsub
      rw [D.crown_left_missing (D.crownParts_symm h) hyR] at hLc
      rw [D.crown_left_missing h hxL] at hRc
      have heq : T = (T ∩ L) ∪ (T ∩ R) := by
        ext z
        have hz := @hsub z
        simp only [Finset.mem_union, Finset.mem_inter] at hz ⊢
        tauto
      have hdis : Disjoint (T ∩ L) (T ∩ R) := h.disjoint.mono Finset.inter_subset_right Finset.inter_subset_right
      have hc := congrArg Finset.card heq
      rw [Finset.card_union_of_disjoint hdis] at hc
      omega

/--
@isnad1 id=eq.2h6v.s7.2c9778051ce0 from=translated src=- shape=f14bd74f vocab=1659be3e
-/
theorem crown_degree {L R : Finset V} (h : D.CrownParts L R) {x : V} (hx : x ∈ L ∪ R) :
    D.neighborCount (L ∪ R) x = 5 := by
  rw [D.neighborCount_union _ _ h.disjoint]
  rcases Finset.mem_union.mp hx with hxL | hxR
  · rw [D.independent_neighborCount_zero h.left_independent hxL,h.left_degree x hxL]
  · rw [D.independent_neighborCount_zero h.right_independent hxR,h.right_degree x hxR]

end SRG266.QuasiSymmetric.TripleDesign57
