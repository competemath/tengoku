import Tengoku.Seed.Data.Finset.Max
import Tengoku.Seed.Data.Finset.Powerset
import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Basic
import Tengoku.Seed.Order.ConditionallyCompleteLattice.Basic
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Finite families of edge sets. These definitions are independent of graph geometry.
Graph triangles are connected to them in the graph module.
-/

namespace Tuza

open Finset

variable {E : Type*} [DecidableEq E]

/-- The union of the edges used by a family.-/
def support (P : Finset (Finset E)) : Finset E := P.biUnion id

/--
@isnad1 id=iff.0h3v.s5.f89ba47d8420 from=translated src=- shape=04c07adf vocab=27f3b8da
-/
@[simp] theorem mem_support {e : E} {P : Finset (Finset E)} :
    e ∈ support P ↔ ∃ T ∈ P, e ∈ T := by
  simp [support]

/--
@isnad1 id=eq.0h3v.s5.585a4e0a2def from=translated src=- shape=2debfcf1 vocab=ac7d3212
-/
@[simp] theorem support_insert (T : Finset E) (P : Finset (Finset E)) :
    support (insert T P) = T ∪ support P := by
  simp [support]

/--
@isnad1 id=le.1h3v.s5.ab4fc719cfb8 from=translated src=- shape=a2fadab1 vocab=850c2929
-/
theorem support_mono {P Q : Finset (Finset E)} (h : P ⊆ Q) :
    support P ⊆ support Q := by
  intro e he
  obtain ⟨T, hT, heT⟩ := mem_support.mp he
  exact mem_support.mpr ⟨T, h hT, heT⟩

/-- A packing consists of members of the family that are pairwise edge-disjoint.-/
def IsPacking (F P : Finset (Finset E)) : Prop :=
  P ⊆ F ∧ (P : Set (Finset E)).Pairwise Disjoint

/-- Maximum is with respect to the number of triangles.-/
def IsMaximumPacking (F P : Finset (Finset E)) : Prop :=
  IsPacking F P ∧ ∀ Q, IsPacking F Q → Q.card ≤ P.card

/-- A transversal meets every member in an edge.-/
def IsCover (F : Finset (Finset E)) (C : Finset E) : Prop :=
  ∀ T ∈ F, (T ∩ C).Nonempty

/-- Deleting selected edges removes every member that meets one of them.-/
def residual (F : Finset (Finset E)) (C : Finset E) : Finset (Finset E) :=
  F.filter (fun T => Disjoint T C)

/--
@isnad1 id=iff.0h4v.s6.958b7da23eb7 from=translated src=- shape=4a7428a6 vocab=7ec92de2
-/
@[simp] theorem mem_residual {F : Finset (Finset E)} {C T : Finset E} :
    T ∈ residual F C ↔ T ∈ F ∧ Disjoint T C := by
  simp [residual]

omit [DecidableEq E] in
/--
@isnad1 id=ispackin.0h2v.s4.7a9d1bd48d55 from=translated src=- shape=c4f41c10 vocab=31054f98
-/
theorem packing_empty (F : Finset (Finset E)) : IsPacking F ∅ := by
  simp [IsPacking, Set.Pairwise]

omit [DecidableEq E] in
/--
@isnad1 id=ispackin.2h4v.s5.295d2e14ca93 from=translated src=- shape=569fbba1 vocab=e8d906c1
-/
theorem IsPacking.subfamily {F P Q : Finset (Finset E)}
    (hP : IsPacking F P) (hQ : Q ⊆ P) : IsPacking F Q := by
  exact ⟨hQ.trans hP.1, fun T hT U hU hne => hP.2 (hQ hT) (hQ hU) hne⟩

omit [DecidableEq E] in
/--
@isnad1 id=ispackin.2h4v.s5.1ab6e0e29ee0 from=translated src=- shape=784ad1ed vocab=e8d906c1
-/
theorem IsPacking.mono_family {F F' P : Finset (Finset E)}
    (hP : IsPacking F P) (hF : F ⊆ F') : IsPacking F' P :=
  ⟨hP.1.trans hF, hP.2⟩

/--
@isnad1 id=ispackin.3h4v.s6.1ce9af896b40 from=translated src=- shape=b8da85fb vocab=8066ba00
-/
theorem IsPacking.union {F P Q : Finset (Finset E)}
    (hP : IsPacking F P) (hQ : IsPacking F Q)
    (hd : Disjoint (support P) (support Q)) : IsPacking F (P ∪ Q) := by
  refine ⟨union_subset hP.1 hQ.1, ?_⟩
  have hcross : ∀ T ∈ P, ∀ U ∈ Q, Disjoint T U := by
    intro T hT U hU
    exact hd.mono (fun e he => mem_support.mpr ⟨T, hT, he⟩)
      (fun e he => mem_support.mpr ⟨U, hU, he⟩)
  intro T hT U hU hne
  rcases mem_union.mp hT with hT | hT <;> rcases mem_union.mp hU with hU | hU
  · exact hP.2 hT hU hne
  · exact hcross T hT U hU
  · exact (hcross U hU T hT).symm
  · exact hQ.2 hT hU hne

/--
@isnad1 id=disjoint.2h3v.s6.c81e1e69d14b from=translated src=- shape=0b22083b vocab=899ab5d2
-/
theorem disjoint_of_support_disjoint {P Q : Finset (Finset E)}
    (hne : ∀ T ∈ P, T.Nonempty) (hd : Disjoint (support P) (support Q)) :
    Disjoint P Q := by
  apply disjoint_left.mpr
  intro T hT hU
  obtain ⟨e, he⟩ := hne T hT
  exact disjoint_left.mp hd (mem_support.mpr ⟨T, hT, he⟩)
    (mem_support.mpr ⟨T, hU, he⟩)

omit [DecidableEq E] in
/--
@isnad1 id=ex.0h2v.s4.5cc62ecfdc5b from=translated src=- shape=327b6ef1 vocab=7176769f
-/
theorem exists_maximumPacking (F : Finset (Finset E)) :
    ∃ P, IsMaximumPacking F P := by
  classical
  let candidates := F.powerset.filter (IsPacking F)
  have hc : (∅ : Finset (Finset E)) ∈ candidates := by
    simp [candidates, packing_empty]
  obtain ⟨P, hP, hmax⟩ := candidates.exists_max_image Finset.card ⟨∅, hc⟩
  refine ⟨P, (mem_filter.mp hP).2, ?_⟩
  intro Q hQ
  exact hmax Q (mem_filter.mpr ⟨mem_powerset.mpr hQ.1, hQ⟩)

/-- One maximum packing, chosen from the finite collection of all packings.-/
noncomputable def maximumPacking (F : Finset (Finset E)) : Finset (Finset E) :=
  Classical.choose (exists_maximumPacking F)

omit [DecidableEq E] in
/--
@isnad1 id=ismaximu.0h2v.s3.8cd16ba37964 from=translated src=- shape=c08fd7c2 vocab=128924fc
-/
theorem maximumPacking_spec (F : Finset (Finset E)) :
    IsMaximumPacking F (maximumPacking F) :=
  Classical.choose_spec (exists_maximumPacking F)

/-- The maximum packing size.-/
noncomputable def packingNumber (F : Finset (Finset E)) : ℕ :=
  (maximumPacking F).card

omit [DecidableEq E] in
/--
@isnad1 id=le.1h3v.s4.dda29a49de13 from=translated src=- shape=f5b501db vocab=37cf200f
-/
theorem IsPacking.card_le {F P : Finset (Finset E)} (hP : IsPacking F P) :
    P.card ≤ packingNumber F :=
  (maximumPacking_spec F).2 P hP

omit [DecidableEq E] in
/--
@isnad1 id=eq.1h3v.s4.7df45a9c9faf from=translated src=- shape=f5b501db vocab=c37047d1
-/
theorem IsMaximumPacking.card_eq {F P : Finset (Finset E)}
    (hP : IsMaximumPacking F P) : P.card = packingNumber F := by
  apply Nat.le_antisymm hP.1.card_le
  exact hP.2 _ (maximumPacking_spec F).1

omit [DecidableEq E] in
/--
@isnad1 id=ismaximu.2h3v.s4.b8669a4b4982 from=translated src=- shape=09a7a0f0 vocab=024e93de
-/
theorem IsPacking.maximum_of_card_eq {F P : Finset (Finset E)}
    (hP : IsPacking F P) (hc : P.card = packingNumber F) :
    IsMaximumPacking F P := by
  refine ⟨hP, fun Q hQ => ?_⟩
  rw [hc]
  exact hQ.card_le

/--
@isnad1 id=ispackin.3h4v.s6.ae1e16bdb464 from=translated src=- shape=69740543 vocab=d3ef91a3
-/
theorem packing_insert {F P : Finset (Finset E)} {T : Finset E}
    (hP : IsPacking F P) (hT : T ∈ F) (hd : Disjoint T (support P)) :
    IsPacking F (insert T P) := by
  refine ⟨insert_subset hT hP.1, ?_⟩
  intro U hU V hV hne
  have hdis : ∀ U ∈ P, Disjoint T U := by
    intro U hU
    exact hd.mono_right (fun e he => mem_support.mpr ⟨U, hU, he⟩)
  simp only [mem_coe, mem_insert] at hU hV
  rcases hU with rfl | hU
  · rcases hV with rfl | hV
    · exact False.elim (hne rfl)
    · exact hdis V hV
  · rcases hV with rfl | hV
    · exact (hdis U hU).symm
    · exact hP.2 hU hV hne

/--
@isnad1 id=nonempty.3h4v.s5.e35726d7a32c from=translated src=- shape=5b3ec62b vocab=5b975e42
-/
theorem IsMaximumPacking.meets_support {F P : Finset (Finset E)}
    (hP : IsMaximumPacking F P) {T : Finset E} (hT : T ∈ F)
    (hne : T.Nonempty) : (T ∩ support P).Nonempty := by
  by_contra hn
  have hd : Disjoint T (support P) := disjoint_iff_inter_eq_empty.mpr
    (not_nonempty_iff_eq_empty.mp hn)
  have hnot : T ∉ P := by
    intro hmem
    obtain ⟨e, he⟩ := hne
    exact disjoint_left.mp hd he (mem_support.mpr ⟨T, hmem, he⟩)
  have hlt := hP.2 (insert T P) (packing_insert hP.1 hT hd)
  simp [hnot] at hlt

/--
@isnad1 id=iscover.2h3v.s5.1b2a4e6c20b0 from=translated src=- shape=887561d5 vocab=fe1d5e12
-/
theorem IsMaximumPacking.support_covers {F P : Finset (Finset E)}
    (hP : IsMaximumPacking F P) (hF : ∀ T ∈ F, T.Nonempty) :
    IsCover F (support P) :=
  fun T hT => hP.meets_support hT (hF T hT)

/--
@isnad1 id=disjoint.3h5v.s6.268130222514 from=translated src=- shape=c2fa2039 vocab=24cb7028
-/
theorem IsPacking.disjoint_support_erase {F P : Finset (Finset E)}
    (hP : IsPacking F P) {S T : Finset E} (hS : S ∈ P)
    (hT : ∀ e ∈ T, e ∈ support P → e ∈ S) :
    Disjoint T (support (P.erase S)) := by
  apply disjoint_left.mpr
  intro e heT heP
  obtain ⟨U, hU, heU⟩ := mem_support.mp heP
  obtain ⟨hUS, hUP⟩ := mem_erase.mp hU
  have heS := hT e heT (mem_support.mpr ⟨U, hUP, heU⟩)
  exact disjoint_left.mp (hP.2 hUP hS hUS) heU heS

/-- Replacing one member of a maximum packing by two disjoint members is impossible.
@isnad1 id=false.9h6v.s7.04f3baa6d0db from=translated src=- shape=7b2ad9ec vocab=390c852a
-/
theorem IsMaximumPacking.no_two_for_one {F P : Finset (Finset E)}
    (hP : IsMaximumPacking F P) {S T U : Finset E}
    (hS : S ∈ P) (hT : T ∈ F) (hU : U ∈ F)
    (hneT : T.Nonempty) (hneU : U.Nonempty) (hdTU : Disjoint T U)
    (hdT : Disjoint T (support (P.erase S)))
    (hdU : Disjoint U (support (P.erase S))) : False := by
  have hbase := hP.1.subfamily (erase_subset S P)
  have hfirst := packing_insert hbase hT hdT
  have hsecond : IsPacking F (insert U (insert T (P.erase S))) := by
    apply packing_insert hfirst hU
    rw [support_insert]
    exact disjoint_union_right.mpr ⟨hdTU.symm, hdU⟩
  have ht : T ∉ P.erase S := by
    intro hmem
    obtain ⟨e, he⟩ := hneT
    exact disjoint_left.mp hdT he (mem_support.mpr ⟨T, hmem, he⟩)
  have hu : U ∉ P.erase S := by
    intro hmem
    obtain ⟨e, he⟩ := hneU
    exact disjoint_left.mp hdU he (mem_support.mpr ⟨U, hmem, he⟩)
  have hUT : U ≠ T := by
    rintro rfl
    obtain ⟨e, he⟩ := hneU
    exact disjoint_left.mp hdTU he he
  have hbound := hP.2 _ hsecond
  have hsize := card_erase_add_one hS
  simp only [card_insert_of_notMem ht,
    card_insert_of_notMem (by simp [hu, hUT] : U ∉ insert T (P.erase S))] at hbound
  omega

/--
@isnad1 id=iscover.1h2v.s5.3cae746dbb1c from=translated src=- shape=648c856c vocab=56ad60b4
-/
theorem support_covers (F : Finset (Finset E))
    (hF : ∀ T ∈ F, T.Nonempty) : IsCover F (support F) := by
  intro T hT
  obtain ⟨e, he⟩ := hF T hT
  exact ⟨e, mem_inter.mpr ⟨he, mem_support.mpr ⟨T, hT, he⟩⟩⟩

/-- Minimum transversal size; the theorems below ensure attainment for
families of nonempty edge sets, in particular for triangle families.-/
noncomputable def transversalNumber (F : Finset (Finset E)) : ℕ :=
  sInf {n : ℕ | ∃ C : Finset E, IsCover F C ∧ C.card = n}

/--
@isnad1 id=le.1h3v.s4.f167d03eb314 from=translated src=- shape=7e0bcf0a vocab=e3dcfb65
-/
theorem IsCover.number_le {F : Finset (Finset E)} {C : Finset E}
    (hC : IsCover F C) : transversalNumber F ≤ C.card := by
  exact csInf_le (OrderBot.bddBelow _) ⟨C, hC, rfl⟩

/--
@isnad1 id=ex.1h2v.s5.565700b8e712 from=translated src=- shape=c49a3c75 vocab=bc11b580
-/
theorem exists_minimumCover (F : Finset (Finset E))
    (hF : ∀ T ∈ F, T.Nonempty) :
    ∃ C, IsCover F C ∧ C.card = transversalNumber F := by
  have hex : {n : ℕ | ∃ C : Finset E, IsCover F C ∧ C.card = n}.Nonempty :=
    ⟨(support F).card, support F, support_covers F hF, rfl⟩
  exact csInf_mem hex

/--
@isnad1 id=iscover.2h4v.s5.24656616dde6 from=translated src=- shape=5b5b5cbf vocab=0f774a4f
-/
theorem IsCover.mono {F : Finset (Finset E)} {C D : Finset E}
    (hC : IsCover F C) (hCD : C ⊆ D) : IsCover F D := by
  intro T hT
  obtain ⟨e, he⟩ := hC T hT
  exact ⟨e, mem_inter.mpr ⟨(mem_inter.mp he).1, hCD (mem_inter.mp he).2⟩⟩

/--
@isnad1 id=iscover.2h4v.s5.f4c0b8e07c4e from=translated src=- shape=73859c26 vocab=0f774a4f
-/
theorem IsCover.mono_family {F F' : Finset (Finset E)} {C : Finset E}
    (hC : IsCover F C) (hF : F' ⊆ F) : IsCover F' C :=
  fun T hT => hC T (hF hT)

/-- Extraneous edges never help a transversal: every cover can be restricted
to the edges that actually occur in the family.
@isnad1 id=iscover.1h3v.s5.9a6c860f2cba from=translated src=- shape=59221252 vocab=10a6a77c
-/
theorem IsCover.inter_support {F : Finset (Finset E)} {C : Finset E}
    (hC : IsCover F C) : IsCover F (C ∩ support F) := by
  intro T hT
  obtain ⟨e, he⟩ := hC T hT
  obtain ⟨heT, heC⟩ := mem_inter.mp he
  exact ⟨e, mem_inter.mpr ⟨heT,
    mem_inter.mpr ⟨heC, mem_support.mpr ⟨T, hT, heT⟩⟩⟩⟩

/--
@isnad1 id=ex.1h2v.s6.fd7dcdf201b7 from=translated src=- shape=bc7be930 vocab=f18ed640
-/
theorem exists_minimumCover_subset_support (F : Finset (Finset E))
    (hF : ∀ T ∈ F, T.Nonempty) :
    ∃ C, C ⊆ support F ∧ IsCover F C ∧ C.card = transversalNumber F := by
  obtain ⟨C, hC, hc⟩ := exists_minimumCover F hF
  refine ⟨C ∩ support F, inter_subset_right, hC.inter_support, ?_⟩
  exact Nat.le_antisymm ((card_le_card inter_subset_left).trans_eq hc)
    hC.inter_support.number_le

/--
@isnad1 id=iscover.1h4v.s5.2e98d24472b1 from=translated src=- shape=e214c6a1 vocab=c47656ff
-/
theorem cover_union_residual {F : Finset (Finset E)} {C D : Finset E}
    (hD : IsCover (residual F C) D) : IsCover F (C ∪ D) := by
  intro T hT
  by_cases hd : Disjoint T C
  · obtain ⟨e, he⟩ := hD T (mem_residual.mpr ⟨hT, hd⟩)
    exact ⟨e, mem_inter.mpr ⟨(mem_inter.mp he).1,
      mem_union_right _ (mem_inter.mp he).2⟩⟩
  · obtain ⟨e, heT, heC⟩ := not_disjoint_iff.mp hd
    exact ⟨e, mem_inter.mpr ⟨heT, mem_union_left _ heC⟩⟩

/--
@isnad1 id=le.1h3v.s5.a61acc2d5d4d from=translated src=- shape=c5b7bc88 vocab=d21cf047
-/
theorem transversalNumber_le_add_residual (F : Finset (Finset E)) (C : Finset E)
    (hF : ∀ T ∈ F, T.Nonempty) :
    transversalNumber F ≤ C.card + transversalNumber (residual F C) := by
  obtain ⟨D, hD, hcard⟩ := exists_minimumCover (residual F C)
    (fun T hT => hF T (mem_residual.mp hT).1)
  calc
    transversalNumber F ≤ (C ∪ D).card := (cover_union_residual hD).number_le
    _ ≤ C.card + D.card := card_union_le C D
    _ = _ := by rw [hcard]

/--
@isnad1 id=eq.1h3v.s5.406e435ca642 from=translated src=- shape=f3107834 vocab=f5437f79
-/
theorem IsPacking.card_support {F P : Finset (Finset E)} (hP : IsPacking F P) :
    (support P).card = ∑ T ∈ P, T.card := by
  exact card_biUnion hP.2

/--
@isnad1 id=eq.2h4v.s6.4b5fd8038cab from=translated src=- shape=e4ad1885 vocab=6969b57d
-/
theorem IsPacking.card_support_uniform {F P : Finset (Finset E)}
    (hP : IsPacking F P) {k : ℕ} (hcard : ∀ T ∈ P, T.card = k) :
    (support P).card = k * P.card := by
  rw [hP.card_support]
  calc
    ∑ T ∈ P, T.card = ∑ _T ∈ P, k := sum_congr rfl hcard
    _ = k * P.card := by simp [Nat.mul_comm]

/--
@isnad1 id=le.1h2v.s5.3a4e280d0b0c from=translated src=- shape=ef2389c2 vocab=b1478dd9
-/
theorem transversalNumber_le_three_packingNumber (F : Finset (Finset E))
    (hF : ∀ T ∈ F, T.card = 3) :
    transversalNumber F ≤ 3 * packingNumber F := by
  have hne : ∀ T ∈ F, T.Nonempty := by
    intro T hT
    exact card_pos.mp (by rw [hF T hT]; decide)
  have hP := maximumPacking_spec F
  calc
    transversalNumber F ≤ (support (maximumPacking F)).card :=
      (hP.support_covers hne).number_le
    _ = 3 * packingNumber F :=
      hP.1.card_support_uniform (fun T hT => hF T (hP.1.1 hT))

/-- First maximize the number of members in S, then the total packing size.-/
def IsLexMaximumPacking (F S P : Finset (Finset E)) : Prop :=
  IsPacking F P ∧ ∀ Q, IsPacking F Q →
    (Q ∩ S).card ≤ (P ∩ S).card ∧
    ((Q ∩ S).card = (P ∩ S).card → Q.card ≤ P.card)

/--
@isnad1 id=ex.0h3v.s4.af8c85837f32 from=translated src=- shape=f3f4f8ba vocab=aab516fc
-/
theorem exists_lexMaximumPacking (F S : Finset (Finset E)) :
    ∃ P, IsLexMaximumPacking F S P := by
  classical
  let candidates := F.powerset.filter (IsPacking F)
  have hc : (∅ : Finset (Finset E)) ∈ candidates := by
    simp [candidates, packing_empty]
  obtain ⟨P₀, hP₀, hmax₀⟩ := candidates.exists_max_image
    (fun P => (P ∩ S).card) ⟨∅, hc⟩
  let tied := candidates.filter (fun P => (P ∩ S).card = (P₀ ∩ S).card)
  have htied : P₀ ∈ tied := by simp [tied, hP₀]
  obtain ⟨P, hP, hmax⟩ := tied.exists_max_image Finset.card ⟨P₀, htied⟩
  obtain ⟨hPc, hPeq⟩ := mem_filter.mp hP
  refine ⟨P, (mem_filter.mp hPc).2, ?_⟩
  intro Q hQ
  have hQc : Q ∈ candidates := mem_filter.mpr ⟨mem_powerset.mpr hQ.1, hQ⟩
  refine ⟨?_, ?_⟩
  · rw [hPeq]
    exact hmax₀ Q hQc
  · intro hQeq
    exact hmax Q (mem_filter.mpr ⟨hQc, hQeq.trans hPeq⟩)

/--
@isnad1 id=ismaximu.2h4v.s6.96e2128155aa from=translated src=- shape=8546428a vocab=7658301d
-/
theorem IsLexMaximumPacking.typePart_maximum {F S P : Finset (Finset E)}
    (hP : IsLexMaximumPacking F S P) (hSF : S ⊆ F) :
    IsMaximumPacking S (P ∩ S) := by
  have hp : IsPacking S (P ∩ S) :=
    ⟨inter_subset_right, fun T hT U hU hne =>
      hP.1.2 (mem_inter.mp hT).1 (mem_inter.mp hU).1 hne⟩
  refine ⟨hp, fun Q hQ => ?_⟩
  have hbound := (hP.2 Q (hQ.mono_family hSF)).1
  simpa [inter_eq_left.mpr hQ.1] using hbound

/--
@isnad1 id=nonempty.3h5v.s5.77a1a8f402d2 from=translated src=- shape=025f6923 vocab=59d0628b
-/
theorem IsLexMaximumPacking.meets_support {F S P : Finset (Finset E)}
    (hP : IsLexMaximumPacking F S P) {T : Finset E}
    (hT : T ∈ F) (hne : T.Nonempty) : (T ∩ support P).Nonempty := by
  by_contra hn
  have hd : Disjoint T (support P) := disjoint_iff_inter_eq_empty.mpr
    (not_nonempty_iff_eq_empty.mp hn)
  have hnot : T ∉ P := by
    intro hmem
    obtain ⟨e, he⟩ := hne
    exact disjoint_left.mp hd he (mem_support.mpr ⟨T, hmem, he⟩)
  have hins := packing_insert hP.1 hT hd
  have hlex := hP.2 (insert T P) hins
  have hmono : (P ∩ S).card ≤ (insert T P ∩ S).card :=
    card_le_card (inter_subset_inter (subset_insert T P) Subset.rfl)
  have heq := Nat.le_antisymm hlex.1 hmono
  have hcard := hlex.2 heq
  simp [hnot] at hcard

/--
@isnad1 id=iscover.2h4v.s5.3e19a785869a from=translated src=- shape=e544f4ed vocab=360b3999
-/
theorem IsLexMaximumPacking.support_covers {F S P : Finset (Finset E)}
    (hP : IsLexMaximumPacking F S P) (hF : ∀ T ∈ F, T.Nonempty) :
    IsCover F (support P) :=
  fun T hT => hP.meets_support hT (hF T hT)

/-- Any packing with the same two optimal counts retains the same maximality.
@isnad1 id=islexmax.4h5v.s6.2da51433ceba from=translated src=- shape=00eb512a vocab=c32dcf23
-/
theorem IsLexMaximumPacking.of_same_counts {F S P Q : Finset (Finset E)}
    (hP : IsLexMaximumPacking F S P) (hQ : IsPacking F Q)
    (hfirst : (Q ∩ S).card = (P ∩ S).card) (hsecond : Q.card = P.card) :
    IsLexMaximumPacking F S Q := by
  refine ⟨hQ, fun U hU => ?_⟩
  obtain ⟨hu₁, hu₂⟩ := hP.2 U hU
  rw [hfirst, hsecond]
  exact ⟨hu₁, hu₂⟩

end Tuza
