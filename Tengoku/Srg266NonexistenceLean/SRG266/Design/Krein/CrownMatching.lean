/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Design.Krein.Crown

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators Matrix

namespace SRG266.QuasiSymmetric.TripleDesign57

variable {P B : Type*} [Fintype P] [DecidableEq P] [Fintype B] [DecidableEq B]
    (D : TripleDesign57 P B)

local notation "V" => KreinVertex (P := P) (B := B)

/--
@isnad1 id=crownpar.1h5v.s5.69531a578bd3 from=translated src=- shape=bc6199b6 vocab=2e2d6530
-/
theorem crownParts_symm {L R : Finset V} (h : D.CrownParts L R) : D.CrownParts R L :=
  ⟨h.right_card,h.left_card,h.disjoint.symm,h.right_independent,h.left_independent,
    h.right_degree,h.left_degree⟩

/--
@isnad1 id=eq.2h6v.s7.24fbc8f53951 from=translated src=- shape=87f9d824 vocab=a2bbe65e
-/
theorem crown_left_missing {L R : Finset V} (h : D.CrownParts L R)
    {x : V} (hx : x ∈ L) : (R.filter fun y => ¬ D.kreinGraph.Adj x y).card = 1 := by
  have hsum := Finset.card_filter_add_card_filter_not (s := R) (p := fun y => D.kreinGraph.Adj x y)
  change D.neighborCount R x + (R.filter fun y => ¬ D.kreinGraph.Adj x y).card = R.card at hsum
  rw [h.left_degree x hx, h.right_card] at hsum
  omega

/--
@isnad1 id=ex.2h6v.s6.af368393a0d8 from=translated src=- shape=e9f46773 vocab=de36e5f6
-/
theorem crown_missing_exists {L R : Finset V} (h : D.CrownParts L R)
    {x : V} (hx : x ∈ L) : ∃ y, y ∈ R ∧ ¬ D.kreinGraph.Adj x y := by
  have hc := D.crown_left_missing h hx
  obtain ⟨y,hy⟩ := Finset.card_pos.mp (by omega : 0 < (R.filter fun y => ¬ D.kreinGraph.Adj x y).card)
  exact ⟨y,(Finset.mem_filter.mp hy).1,(Finset.mem_filter.mp hy).2⟩

noncomputable def crownMate {L R : Finset V} (h : D.CrownParts L R) (x : V) : V :=
  if hx : x ∈ L then Classical.choose (D.crown_missing_exists h hx) else none

/--
@isnad1 id=and.2h6v.s7.75d5cfc00bc5 from=translated src=- shape=bbfe0793 vocab=42f45efa
-/
theorem crownMate_spec {L R : Finset V} (h : D.CrownParts L R) {x : V} (hx : x ∈ L) :
    D.crownMate h x ∈ R ∧ ¬ D.kreinGraph.Adj x (D.crownMate h x) := by
  simp only [crownMate, dite_eq_left hx]
  exact Classical.choose_spec (D.crown_missing_exists h hx)

/--
@isnad1 id=eq.4h7v.s7.eb394739ac8e from=translated src=- shape=2a46b014 vocab=42f45efa
-/
theorem crownMate_unique {L R : Finset V} (h : D.CrownParts L R) {x y : V}
    (hx : x ∈ L) (hy : y ∈ R) (hn : ¬ D.kreinGraph.Adj x y) : y = D.crownMate h x := by
  have hc : (R.filter fun z => ¬ D.kreinGraph.Adj x z).card ≤ 1 := by
    rw [D.crown_left_missing h hx]
  exact Finset.card_le_one.mp hc y (Finset.mem_filter.mpr ⟨hy,hn⟩)
    (D.crownMate h x) (Finset.mem_filter.mpr (D.crownMate_spec h hx))

/--
@isnad1 id=injon.1h5v.s6.e5bbc191025b from=translated src=- shape=45928026 vocab=ec149f4b
-/
theorem crownMate_injOn {L R : Finset V} (h : D.CrownParts L R) :
    Set.InjOn (D.crownMate h) L := by
  intro x hx y hy heq
  have hmx := D.crownMate_spec h hx
  have hmy := D.crownMate_spec h hy
  rw [← heq] at hmy
  have hc : (L.filter fun z => ¬ D.kreinGraph.Adj (D.crownMate h x) z).card ≤ 1 := by
    rw [D.crown_left_missing (D.crownParts_symm h) hmx.1]
  exact Finset.card_le_one.mp hc x
    (Finset.mem_filter.mpr ⟨hx,fun ha => hmx.2 ((D.kreinGraph.adj_comm _ _).mp ha)⟩) y
    (Finset.mem_filter.mpr ⟨hy,fun ha => hmy.2 ((D.kreinGraph.adj_comm _ _).mp ha)⟩)

/--
@isnad1 id=le.2h6v.s7.b91e285254a0 from=translated src=- shape=e9538bf3 vocab=fcc9bb43
-/
theorem crownMate_image_subset {L R T : Finset V} (h : D.CrownParts L R) (hTL : T ⊆ L) :
    T.image (D.crownMate h) ⊆ R := by
  intro y hy
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
  exact (D.crownMate_spec h (hTL hx)).1

/--
@isnad1 id=eq.2h6v.s7.219bfcd7ebee from=translated src=- shape=edf87fd8 vocab=cdee5700
-/
theorem crownMate_image_card {L R T : Finset V} (h : D.CrownParts L R) (hTL : T ⊆ L) :
    (T.image (D.crownMate h)).card = T.card :=
  Finset.card_image_of_injOn (fun _ hx _ hy heq => D.crownMate_injOn h (hTL hx) (hTL hy) heq)

/--
@isnad1 id=eq.1h5v.s6.ae283fa2ec46 from=translated src=- shape=0c4408a2 vocab=15f8537f
-/
theorem crownMate_image_all {L R : Finset V} (h : D.CrownParts L R) :
    L.image (D.crownMate h) = R := by
  apply Finset.eq_of_subset_of_card_le (D.crownMate_image_subset h Finset.Subset.rfl)
  rw [D.crownMate_image_card h Finset.Subset.rfl, h.left_card, h.right_card]

/--
@isnad1 id=iff.3h7v.s7.c96afced469e from=translated src=- shape=0bc25da9 vocab=42f45efa
-/
theorem crown_adj_iff {L R : Finset V} (h : D.CrownParts L R) {x y : V}
    (hx : x ∈ L) (hy : y ∈ R) : D.kreinGraph.Adj x y ↔ y ≠ D.crownMate h x := by
  constructor
  · intro ha heq
    exact (D.crownMate_spec h hx).2 (heq ▸ ha)
  · intro hne
    by_contra hn
    exact hne (D.crownMate_unique h hx hy hn)

/--
@isnad1 id=eq.4h7v.s7.6f8e28a2f774 from=translated src=- shape=3f712903 vocab=07c66d0f
-/
theorem crown_commonCount_pair {L R : Finset V} (h : D.CrownParts L R)
    {x y : V} (hx : x ∈ L) (hy : y ∈ L) (hxy : x ≠ y) :
    D.commonCount (L ∪ R) x y = 4 := by
  have hmxy : D.crownMate h x ≠ D.crownMate h y := fun heq => hxy (D.crownMate_injOn h hx hy heq)
  have hsub : {D.crownMate h x,D.crownMate h y} ⊆ R := by
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with hz | hz
    · rw [hz]; exact (D.crownMate_spec h hx).1
    · rw [hz]; exact (D.crownMate_spec h hy).1
  have heq : (L ∪ R).filter (fun z => D.kreinGraph.Adj x z ∧ D.kreinGraph.Adj y z) =
      R \ {D.crownMate h x,D.crownMate h y} := by
    ext z
    constructor
    · intro hz
      obtain ⟨hzW,hxz,hyz⟩ := Finset.mem_filter.mp hz
      have hzR : z ∈ R := by
        rcases Finset.mem_union.mp hzW with hzL | hzR
        · exact (h.left_independent x hx z hzL (D.kreinGraph.ne_of_adj hxz) hxz).elim
        · exact hzR
      refine Finset.mem_sdiff.mpr ⟨hzR,?_⟩
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
      exact ⟨(D.crown_adj_iff h hx hzR).mp hxz,(D.crown_adj_iff h hy hzR).mp hyz⟩
    · intro hz
      obtain ⟨hzR,hznot⟩ := Finset.mem_sdiff.mp hz
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hznot
      exact Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hzR,
        (D.crown_adj_iff h hx hzR).mpr hznot.1,(D.crown_adj_iff h hy hzR).mpr hznot.2⟩
  rw [commonCount, heq, Finset.card_sdiff_of_subset hsub, h.right_card]
  simp [hmxy]

end SRG266.QuasiSymmetric.TripleDesign57
