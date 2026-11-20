import Tengoku.TuzaLean.Tuza.Basic.Packing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Red and blue edges in finite families of three-edge sets. -/

namespace Tuza

open Finset

variable {E : Type*} [DecidableEq E]

/-- The red edges used by a family.-/
def redEdges (R : Finset E) (P : Finset (Finset E)) : Finset E :=
  support P ∩ R

/-- Every edge outside the specified red set is blue.-/
def blueEdges (R : Finset E) (P : Finset (Finset E)) : Finset E :=
  support P \ R

/-- Each member has exactly three edges, exactly one of which is red.-/
def ColoredFamily (F : Finset (Finset E)) (R : Finset E) : Prop :=
  ∀ T ∈ F, T.card = 3 ∧ (T ∩ R).card = 1

/--
@isnad1 id=iff.0h4v.s5.8770f9e9410c from=translated src=- shape=ae6dcc8a vocab=475211d5
-/
@[simp] theorem mem_redEdges {R : Finset E} {P : Finset (Finset E)} {e : E} :
    e ∈ redEdges R P ↔ e ∈ support P ∧ e ∈ R := by
  simp [redEdges]

/--
@isnad1 id=iff.0h4v.s5.a029c40dae59 from=translated src=- shape=7596a7da vocab=1b3fa2ef
-/
@[simp] theorem mem_blueEdges {R : Finset E} {P : Finset (Finset E)} {e : E} :
    e ∈ blueEdges R P ↔ e ∈ support P ∧ e ∉ R := by
  simp [blueEdges]

/--
@isnad1 id=le.0h3v.s5.b223e354306c from=translated src=- shape=a6fae5d6 vocab=1d713a44
-/
theorem redEdges_subset_support (R : Finset E) (P : Finset (Finset E)) :
    redEdges R P ⊆ support P := inter_subset_left

/--
@isnad1 id=le.0h3v.s4.ded619352f5c from=translated src=- shape=b44efb53 vocab=cca8529c
-/
theorem redEdges_subset_red (R : Finset E) (P : Finset (Finset E)) :
    redEdges R P ⊆ R := inter_subset_right

/--
@isnad1 id=le.0h3v.s5.86bd0f0acf05 from=translated src=- shape=a6fae5d6 vocab=a6906eeb
-/
theorem blueEdges_subset_support (R : Finset E) (P : Finset (Finset E)) :
    blueEdges R P ⊆ support P := sdiff_subset

/--
@isnad1 id=disjoint.0h3v.s4.d0a513bdf342 from=translated src=- shape=762c955d vocab=cac4e942
-/
theorem redEdges_disjoint_blueEdges (R : Finset E) (P : Finset (Finset E)) :
    Disjoint (redEdges R P) (blueEdges R P) := by
  apply disjoint_left.mpr
  intro e heR heB
  exact (mem_blueEdges.mp heB).2 (mem_redEdges.mp heR).2

/--
@isnad1 id=disjoint.0h3v.s4.d45c714a85de from=translated src=- shape=b44efb53 vocab=5b9f2dd4
-/
theorem blueEdges_disjoint_red (R : Finset E) (P : Finset (Finset E)) :
    Disjoint (blueEdges R P) R := by
  apply disjoint_left.mpr
  intro e heB heR
  exact (mem_blueEdges.mp heB).2 heR

/--
@isnad1 id=eq.0h3v.s5.3f891b1b2119 from=translated src=- shape=8d391817 vocab=6bd1ec44
-/
@[simp] theorem redEdges_union_blueEdges (R : Finset E) (P : Finset (Finset E)) :
    redEdges R P ∪ blueEdges R P = support P := by
  ext e
  by_cases he : e ∈ R <;> simp [redEdges, blueEdges, he]

/--
@isnad1 id=eq.0h3v.s5.e80f61355757 from=translated src=- shape=53967ca2 vocab=3933873a
-/
theorem card_blueEdges_add_card_redEdges (R : Finset E) (P : Finset (Finset E)) :
    (blueEdges R P).card + (redEdges R P).card = (support P).card := by
  exact card_sdiff_add_card_inter (support P) R

/--
@isnad1 id=eq.0h3v.s5.d855b5134b79 from=translated src=- shape=fbce9e69 vocab=6d5b3c39
-/
theorem redEdges_eq_biUnion (R : Finset E) (P : Finset (Finset E)) :
    redEdges R P = P.biUnion (fun T => T ∩ R) := by
  ext e
  constructor
  · intro he
    obtain ⟨heP, heR⟩ := mem_redEdges.mp he
    obtain ⟨T, hT, heT⟩ := mem_support.mp heP
    exact mem_biUnion.mpr ⟨T, hT, mem_inter.mpr ⟨heT, heR⟩⟩
  · intro he
    obtain ⟨T, hT, heTR⟩ := mem_biUnion.mp he
    obtain ⟨heT, heR⟩ := mem_inter.mp heTR
    exact mem_redEdges.mpr ⟨mem_support.mpr ⟨T, hT, heT⟩, heR⟩

/--
@isnad1 id=coloredf.2h4v.s5.15ae24bc4a07 from=translated src=- shape=73859c26 vocab=9bdff17e
-/
theorem ColoredFamily.subfamily {F F' : Finset (Finset E)} {R : Finset E}
    (hF : ColoredFamily F R) (hsub : F' ⊆ F) : ColoredFamily F' R :=
  fun T hT => hF T (hsub hT)

/--
@isnad1 id=coloredf.1h4v.s4.07762481171e from=translated src=- shape=6994a435 vocab=54de6d66
-/
theorem ColoredFamily.residual {F : Finset (Finset E)} {R C : Finset E}
    (hF : ColoredFamily F R) : ColoredFamily (residual F C) R :=
  hF.subfamily (filter_subset _ _)

/--
@isnad1 id=nonempty.2h4v.s5.21e3aea6963b from=translated src=- shape=1de0d175 vocab=1b019e0f
-/
theorem ColoredFamily.member_nonempty {F : Finset (Finset E)} {R T : Finset E}
    (hF : ColoredFamily F R) (hT : T ∈ F) : T.Nonempty := by
  apply card_pos.mp
  rw [(hF T hT).1]
  decide

/--
@isnad1 id=eq.2h4v.s5.d9ef29efd185 from=translated src=- shape=4bb9b245 vocab=8323e891
-/
theorem ColoredFamily.member_blue_card {F : Finset (Finset E)} {R T : Finset E}
    (hF : ColoredFamily F R) (hT : T ∈ F) : (T \ R).card = 2 := by
  have hsum := card_sdiff_add_card_inter T R
  obtain ⟨hthree, hone⟩ := hF T hT
  omega

/--
@isnad1 id=eq.4h5v.s6.5b0376bc5295 from=translated src=- shape=633d0e27 vocab=3b601694
-/
theorem ColoredFamily.red_eq_singleton {F : Finset (Finset E)} {R T : Finset E}
    {e : E} (hF : ColoredFamily F R) (hT : T ∈ F) (heT : e ∈ T) (heR : e ∈ R) :
    T ∩ R = {e} := by
  obtain ⟨r, hr⟩ := card_eq_one.mp (hF T hT).2
  have he : e ∈ ({r} : Finset E) := hr ▸ mem_inter.mpr ⟨heT, heR⟩
  have her : e = r := mem_singleton.mp he
  subst e
  exact hr

/-- Different members of a packing have different singleton red intersections.
@isnad1 id=eq.5h6v.s6.fa55050a991f from=translated src=- shape=ee74abca vocab=8c879d77
-/
theorem IsPacking.red_inter_injective {F P : Finset (Finset E)} {R : Finset E}
    (hP : IsPacking F P) (hF : ColoredFamily F R) {T U : Finset E}
    (hT : T ∈ P) (hU : U ∈ P) (heq : T ∩ R = U ∩ R) : T = U := by
  by_contra hne
  have hn : (T ∩ R).Nonempty := card_pos.mp (by rw [(hF T (hP.1 hT)).2]; decide)
  obtain ⟨e, he⟩ := hn
  have heU : e ∈ U ∩ R := heq ▸ he
  exact disjoint_left.mp (hP.2 hT hU hne) (mem_inter.mp he).1 (mem_inter.mp heU).1

/--
@isnad1 id=eq.2h4v.s5.0aa536b6979e from=translated src=- shape=59bcb959 vocab=ca9f2d91
-/
theorem IsPacking.card_redEdges {F P : Finset (Finset E)} {R : Finset E}
    (hP : IsPacking F P) (hF : ColoredFamily F R) :
    (redEdges R P).card = P.card := by
  rw [redEdges_eq_biUnion]
  have hd : (P : Set (Finset E)).Pairwise
      (fun T U => Disjoint (T ∩ R) (U ∩ R)) := by
    intro T hT U hU hne
    exact (hP.2 hT hU hne).mono inter_subset_left inter_subset_left
  rw [card_biUnion hd]
  calc
    ∑ T ∈ P, (T ∩ R).card = ∑ _T ∈ P, 1 := by
      apply sum_congr rfl
      intro T hT
      exact (hF T (hP.1 hT)).2
    _ = P.card := by simp

/--
@isnad1 id=eq.2h4v.s5.c815f5b9fc75 from=translated src=- shape=4a2777eb vocab=3b491cb8
-/
theorem IsPacking.card_blueEdges {F P : Finset (Finset E)} {R : Finset E}
    (hP : IsPacking F P) (hF : ColoredFamily F R) :
    (blueEdges R P).card = 2 * P.card := by
  have hsum := card_blueEdges_add_card_redEdges R P
  have hred := hP.card_redEdges hF
  have hsupport := hP.card_support_uniform (fun T hT => (hF T (hP.1 hT)).1)
  omega

/-- A residual member meets the parent support precisely in its unique red
edge. Maximality supplies a nonempty intersection; the color count identifies it.
@isnad1 id=eq.3h5v.s6.d6c0e1559028 from=translated src=- shape=ba3b343c vocab=7ff4d402
-/
theorem residual_inter_support_eq_inter_red {F P : Finset (Finset E)}
    {R T : Finset E} (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hT : T ∈ residual F (blueEdges R P)) : T ∩ support P = T ∩ R := by
  obtain ⟨hTF, hdis⟩ := mem_residual.mp hT
  have hsub : T ∩ support P ⊆ T ∩ R := by
    intro e he
    obtain ⟨heT, heP⟩ := mem_inter.mp he
    refine mem_inter.mpr ⟨heT, ?_⟩
    by_contra heR
    exact disjoint_left.mp hdis heT (mem_blueEdges.mpr ⟨heP, heR⟩)
  apply Subset.antisymm hsub
  intro e he
  obtain ⟨f, hf⟩ := hP.meets_support hTF (hF.member_nonempty hTF)
  have hsmall : (T ∩ R).card ≤ 1 := by rw [(hF T hTF).2]
  have hef : e = f := card_le_one.mp hsmall e he f (hsub hf)
  subst e
  exact hf

/-- The residual consists of the family members meeting the parent support
exactly in their red edge.
@isnad1 id=iff.2h5v.s6.912eabb90d51 from=translated src=- shape=e15a6c27 vocab=7ff4d402
-/
theorem mem_residual_blueEdges_iff {F P : Finset (Finset E)} {R T : Finset E}
    (hF : ColoredFamily F R) (hP : IsMaximumPacking F P) :
    T ∈ residual F (blueEdges R P) ↔ T ∈ F ∧ T ∩ support P = T ∩ R := by
  constructor
  · intro hT
    exact ⟨(mem_residual.mp hT).1, residual_inter_support_eq_inter_red hF hP hT⟩
  · rintro ⟨hTF, heq⟩
    refine mem_residual.mpr ⟨hTF, disjoint_left.mpr ?_⟩
    intro e heT heB
    obtain ⟨heP, heR⟩ := mem_blueEdges.mp heB
    have he : e ∈ T ∩ R := heq ▸ mem_inter.mpr ⟨heT, heP⟩
    exact heR (mem_inter.mp he).2

/--
@isnad1 id=le.3h5v.s6.3c3b2125f063 from=translated src=- shape=f29fbb78 vocab=1bb987ed
-/
theorem residual_red_subset_parent_red {F P : Finset (Finset E)} {R T : Finset E}
    (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hT : T ∈ residual F (blueEdges R P)) : T ∩ R ⊆ redEdges R P := by
  intro e he
  have heP : e ∈ T ∩ support P :=
    (residual_inter_support_eq_inter_red hF hP hT).symm ▸ he
  exact mem_redEdges.mpr ⟨(mem_inter.mp heP).2, (mem_inter.mp he).2⟩

/--
@isnad1 id=le.3h5v.s6.1c146dfd1aba from=translated src=- shape=fd29bfd9 vocab=e3e95dc7
-/
theorem IsPacking.redEdges_subset_parent {F P Q : Finset (Finset E)}
    {R : Finset E} (hQ : IsPacking (residual F (blueEdges R P)) Q)
    (hF : ColoredFamily F R) (hP : IsMaximumPacking F P) :
    redEdges R Q ⊆ redEdges R P := by
  intro e he
  obtain ⟨heQ, heR⟩ := mem_redEdges.mp he
  obtain ⟨T, hT, heT⟩ := mem_support.mp heQ
  exact residual_red_subset_parent_red hF hP (hQ.1 hT)
    (mem_inter.mpr ⟨heT, heR⟩)

/-- Blue residual edges avoid the parent support.
@isnad1 id=disjoint.1h5v.s5.a1436e435ba0 from=translated src=- shape=24aa244a vocab=35683f4a
-/
theorem IsPacking.blueEdges_disjoint_parent_support {F P Q : Finset (Finset E)}
    {R : Finset E} (hQ : IsPacking (residual F (blueEdges R P)) Q) :
    Disjoint (blueEdges R Q) (support P) := by
  apply disjoint_left.mpr
  intro e heQ heP
  obtain ⟨heQ, heR⟩ := mem_blueEdges.mp heQ
  obtain ⟨T, hT, heT⟩ := mem_support.mp heQ
  have hdis := (mem_residual.mp (hQ.1 hT)).2
  exact disjoint_left.mp hdis heT (mem_blueEdges.mpr ⟨heP, heR⟩)

/--
@isnad1 id=eq.3h5v.s6.f79bf4f82dc2 from=translated src=- shape=1d83cb5c vocab=eb9f8de3
-/
theorem IsPacking.support_inter_parent_eq_redEdges {F P Q : Finset (Finset E)}
    {R : Finset E} (hQ : IsPacking (residual F (blueEdges R P)) Q)
    (hF : ColoredFamily F R) (hP : IsMaximumPacking F P) :
    support Q ∩ support P = redEdges R Q := by
  ext e
  constructor
  · intro he
    obtain ⟨heQ, heP⟩ := mem_inter.mp he
    refine mem_redEdges.mpr ⟨heQ, ?_⟩
    by_contra heR
    exact disjoint_left.mp hQ.blueEdges_disjoint_parent_support
      (mem_blueEdges.mpr ⟨heQ, heR⟩) heP
  · intro he
    exact mem_inter.mpr ⟨(mem_redEdges.mp he).1,
      (mem_redEdges.mp (hQ.redEdges_subset_parent hF hP he)).1⟩

/-- Packing members whose red edge occurs in no other member of the family.-/
noncomputable def privateRedPages (F : Finset (Finset E)) (R : Finset E)
    (P : Finset (Finset E)) : Finset (Finset E) := by
  classical
  exact P.filter (fun T => ∀ U ∈ F, U ∩ R = T ∩ R → U = T)

/--
@isnad1 id=iff.0h5v.s6.ac558b455763 from=translated src=- shape=8d41efc9 vocab=67110b1f
-/
@[simp] theorem mem_privateRedPages {F P : Finset (Finset E)} {R T : Finset E} :
    T ∈ privateRedPages F R P ↔ T ∈ P ∧ ∀ U ∈ F, U ∩ R = T ∩ R → U = T := by
  classical
  simp [privateRedPages]

/--
@isnad1 id=le.0h4v.s5.f1b978433078 from=translated src=- shape=26e128d1 vocab=6d691e67
-/
theorem privateRedPages_subset (F : Finset (Finset E)) (R : Finset E)
    (P : Finset (Finset E)) : privateRedPages F R P ⊆ P := by
  intro T hT
  exact (mem_privateRedPages.mp hT).1

/-- A cover may omit these private red edges if it contains the corresponding
blue edges. Only their own triangles could lose a selected red edge.
@isnad1 id=iscover.5h6v.s6.15f140693e89 from=translated src=- shape=814aa973 vocab=5150dbaf
-/
theorem IsCover.sdiff_privateRed {F P U : Finset (Finset E)} {R C : Finset E}
    (hC : IsCover F C) (hF : ColoredFamily F R) (hP : IsPacking F P)
    (hU : U ⊆ privateRedPages F R P) (hblue : blueEdges R U ⊆ C) :
    IsCover F (C \ redEdges R U) := by
  intro T hT
  obtain ⟨e, he⟩ := hC T hT
  obtain ⟨heT, heC⟩ := mem_inter.mp he
  by_cases heU : e ∈ redEdges R U
  · obtain ⟨heSupport, heR⟩ := mem_redEdges.mp heU
    obtain ⟨S, hS, heS⟩ := mem_support.mp heSupport
    obtain ⟨hSP, hprivate⟩ := mem_privateRedPages.mp (hU hS)
    have hTS : T = S := hprivate T hT
      ((hF.red_eq_singleton hT heT heR).trans
        (hF.red_eq_singleton (hP.1 hSP) heS heR).symm)
    subst T
    have hblueCard := hF.member_blue_card (hP.1 hSP)
    obtain ⟨f, hf⟩ := card_pos.mp (show 0 < (S \ R).card by omega)
    obtain ⟨hfS, hfR⟩ := mem_sdiff.mp hf
    have hfC := hblue (mem_blueEdges.mpr ⟨mem_support.mpr ⟨S, hS, hfS⟩, hfR⟩)
    exact ⟨f, mem_inter.mpr ⟨hfS, mem_sdiff.mpr ⟨hfC,
      fun hfRed => hfR (mem_redEdges.mp hfRed).2⟩⟩⟩
  · exact ⟨e, mem_inter.mpr ⟨heT, mem_sdiff.mpr ⟨heC, heU⟩⟩⟩

/--
@isnad1 id=eq.4h6v.s6.c3929421ed8d from=translated src=- shape=85cc0d9b vocab=a6cea122
-/
theorem card_sdiff_privateRed {F P U : Finset (Finset E)} {R C : Finset E}
    (hF : ColoredFamily F R) (hP : IsPacking F P)
    (hU : U ⊆ privateRedPages F R P) (hred : redEdges R U ⊆ C) :
    (C \ redEdges R U).card + U.card = C.card := by
  have hpack := hP.subfamily (hU.trans (privateRedPages_subset F R P))
  have hcard := card_sdiff_add_card_inter C (redEdges R U)
  rw [inter_eq_right.mpr hred, hpack.card_redEdges hF] at hcard
  exact hcard

/-- The second colored cover is the parent blue edges and a residual maximum
packing, with every residual-private red edge deleted.
@isnad1 id=le.3h5v.s6.6f244088c347 from=translated src=- shape=1914e32a vocab=d1aa3424
-/
theorem second_colored_cover {F P Q : Finset (Finset E)} {R : Finset E}
    (hF : ColoredFamily F R) (hP : IsPacking F P)
    (hQ : IsMaximumPacking (residual F (blueEdges R P)) Q) :
    transversalNumber F + (privateRedPages (residual F (blueEdges R P)) R Q).card
      ≤ 2 * P.card + 3 * Q.card := by
  let S := residual F (blueEdges R P)
  let U := privateRedPages S R Q
  have hS : ColoredFamily S R := hF.residual
  have hU : U ⊆ privateRedPages S R Q := Subset.refl _
  have hUP : U ⊆ Q := privateRedPages_subset S R Q
  have hcover : IsCover S (support Q) :=
    hQ.support_covers (fun _ hT => hS.member_nonempty hT)
  have hblue : blueEdges R U ⊆ support Q :=
    (blueEdges_subset_support _ _).trans (support_mono hUP)
  have hred : redEdges R U ⊆ support Q :=
    (redEdges_subset_support _ _).trans (support_mono hUP)
  have hremoved := hcover.sdiff_privateRed hS hQ.1 hU hblue
  have hsize := card_sdiff_privateRed hS hQ.1 hU hred
  have hQsize := hQ.1.card_support_uniform (fun T hT => (hS T (hQ.1.1 hT)).1)
  have hPblue := hP.card_blueEdges hF
  have hbound := (cover_union_residual hremoved).number_le
  have hunion := card_union_le (blueEdges R P) (support Q \ redEdges R U)
  change transversalNumber F + U.card ≤ _
  omega

end Tuza
