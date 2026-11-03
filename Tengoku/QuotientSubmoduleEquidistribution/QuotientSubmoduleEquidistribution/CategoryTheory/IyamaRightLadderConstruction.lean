import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.CategoryTheory.IyamaRightLadderPropagation
import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.CategoryTheory.IyamaSpecialMorphism
import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.CategoryTheory.IyamaKrullSchmidtNormalForm
import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.CategoryTheory.SplitMorphismComplement
import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.CategoryTheory.FiniteTauCategory

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The split-complement step in Iyama right ladders

This file isolates the categorical diagram behind Iyama,
*Tau-categories I*, Section 3.2.  A split-monic factor of the current arrow
through a right mesh, together with a padded decomposition of the next raw
arrow, determines all maps and relations in one explicit right-ladder step.
-/

open scoped QuotientSubmoduleEquidistribution.CategoricalIdeal.HomIdeal

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.Iyama.RightLadder

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasBinaryBiproducts C]

/-- A split complement, after changing the complementary object by an
isomorphism and swapping the two factors, identifies the ambient object with
`Y ⊞ source`.-/
def transportedSwappedComplementIso
    {Z M Y : C} {j : Z ⟶ M} [IsSplitMono j]
    (d : SplitMonoComplement j) (e : d.complement ≅ Y) :
    M ≅ Y ⊞ Z where
  hom := biprod.lift (d.projection ≫ e.hom) (retraction j)
  inv := biprod.desc (e.inv ≫ d.inclusion) j
  hom_inv_id := by
    rw [biprod.lift_desc]
    simp only [Category.assoc, e.hom_inv_id_assoc]
    simpa [add_comm] using d.total
  inv_hom_id := by
    ext <;> simp [Category.assoc]
    calc
      e.inv ≫ d.inclusion ≫ d.projection ≫ e.hom =
          e.inv ≫ (d.inclusion ≫ d.projection) ≫ e.hom := by
            simp only [Category.assoc]
      _ = e.inv ≫ CategoryStruct.id d.complement ≫ e.hom := by
        rw [d.inclusion_projection]
      _ = CategoryStruct.id Y := by simp

/-- Invariant one-step extraction from a split mesh factor.

`j` is the split-monic factor of the current essential arrow through `S.g`.
The next raw arrow is `S.f ≫ d.projection`.  The isomorphisms `eX` and `eY`
and the equation `heNext` record its arrow-category isomorphism to the padded
arrow `(bNext, 0)`.  From these data all four horizontal maps and both
relations in Iyama's displayed step are forced, and `S` is isomorphic to the
resulting explicit step complex.

The right endpoint is allowed to be merely isomorphic to `YPrev`, matching
the chosen-mesh interface of `FiniteTauCategoryData`.
@isnad1 id=other.1h13v.s9.dc6c93e0345c from=translated src=- shape=ad6a5c71 vocab=7ada183b
-/
theorem exists_stepComplex_iso_of_split_factor_and_padded_next
    (S : ShortComplex C) {YPrev ZPrev ZNext YNext U : C}
    (ePrev : S.X₃ ≅ YPrev)
    (j : ZPrev ⟶ S.X₂) [IsSplitMono j]
    (d : SplitMonoComplement j)
    (bNext : ZNext ⟶ YNext)
    (eX : S.X₁ ≅ ZNext ⊞ U)
    (eY : d.complement ≅ YNext)
    (heNext :
      (S.f ≫ d.projection) ≫ eY.hom =
        eX.hom ≫ biprod.desc bNext (0 : U ⟶ YNext)) :
    let bPrev : ZPrev ⟶ YPrev := j ≫ S.g ≫ ePrev.hom
    ∃ (f : YNext ⟶ YPrev) (g : ZNext ⟶ ZPrev)
      (h : U ⟶ ZPrev)
      (comm : bNext ≫ f = g ≫ bPrev)
      (hzero : h ≫ bPrev = 0),
        Nonempty
          (S ≅ stepComplex bPrev bNext f g h comm hzero) := by
  dsimp only
  let bPrev : ZPrev ⟶ YPrev := j ≫ S.g ≫ ePrev.hom
  let f : YNext ⟶ YPrev :=
    eY.inv ≫ d.inclusion ≫ S.g ≫ ePrev.hom
  let q : ZNext ⊞ U ⟶ ZPrev :=
    eX.inv ≫ S.f ≫ retraction j
  let g : ZNext ⟶ ZPrev := -(biprod.inl ≫ q)
  let h : U ⟶ ZPrev := biprod.inr ≫ q
  let eM : S.X₂ ≅ YNext ⊞ ZPrev :=
    transportedSwappedComplementIso d eY

  have hq : q = biprod.desc (-g) h := by
    apply biprod.hom_ext'
    · simp [g, q]
    · simp [h, q]

  have hfirst :
      eX.hom ≫
          biprod.desc
            (biprod.lift bNext (-g)) (biprod.lift 0 h) =
        S.f ≫ eM.hom := by
    apply biprod.hom_ext
    · simpa [eM, transportedSwappedComplementIso,
        biprod.desc_eq, Category.assoc] using heNext.symm
    · have hs :
          eX.hom ≫ biprod.desc (-g) h =
            S.f ≫ retraction j := by
        rw [← cancel_epi eX.inv]
        simp only [eX.inv_hom_id_assoc]
        change biprod.desc (-g) h = q
        exact hq.symm
      simpa [eM, transportedSwappedComplementIso,
        biprod.desc_eq, Category.assoc] using hs

  have hsecond :
      eM.hom ≫ biprod.desc f bPrev = S.g ≫ ePrev.hom := by
    change
      biprod.lift (d.projection ≫ eY.hom) (retraction j) ≫
          biprod.desc f bPrev =
        S.g ≫ ePrev.hom
    rw [biprod.lift_desc]
    dsimp only [f, bPrev]
    simp only [Category.assoc]
    rw [eY.hom_inv_id_assoc]
    have htotal :
        d.projection ≫ d.inclusion + retraction j ≫ j =
          CategoryStruct.id S.X₂ := by
      simpa [add_comm] using d.total
    calc
      d.projection ≫ d.inclusion ≫ S.g ≫ ePrev.hom +
            retraction j ≫ j ≫ S.g ≫ ePrev.hom =
          (d.projection ≫ d.inclusion + retraction j ≫ j) ≫
            S.g ≫ ePrev.hom := by
              simp only [Preadditive.add_comp, Category.assoc]
      _ = S.g ≫ ePrev.hom := by rw [htotal]; simp

  let first : ZNext ⊞ U ⟶ YNext ⊞ ZPrev :=
    biprod.desc (biprod.lift bNext (-g)) (biprod.lift 0 h)
  let second : YNext ⊞ ZPrev ⟶ YPrev := biprod.desc f bPrev
  have hzero : first ≫ second = 0 := by
    rw [← cancel_epi eX.hom]
    calc
      eX.hom ≫ (first ≫ second) =
          (eX.hom ≫ first) ≫ second :=
        (Category.assoc _ _ _).symm
      _ = (S.f ≫ eM.hom) ≫ second := by
        simpa only [first] using congrArg (fun k ↦ k ≫ second) hfirst
      _ = S.f ≫ (eM.hom ≫ second) := Category.assoc _ _ _
      _ = S.f ≫ (S.g ≫ ePrev.hom) := by
        simpa only [second] using congrArg (fun k ↦ S.f ≫ k) hsecond
      _ = 0 := by rw [← Category.assoc, S.zero, zero_comp]
      _ = eX.hom ≫ 0 := by simp

  have hcomm : bNext ≫ f = g ≫ bPrev := by
    have hz := congrArg (fun k ↦ biprod.inl ≫ k) hzero
    dsimp only [first, second] at hz
    apply sub_eq_zero.mp
    simpa only [biprod.inl_desc_assoc, biprod.lift_desc,
      Preadditive.neg_comp, comp_zero, sub_eq_add_neg] using hz

  have hhzero : h ≫ bPrev = 0 := by
    have hz := congrArg (fun k ↦ biprod.inr ≫ k) hzero
    dsimp only [first, second] at hz
    simpa [Category.assoc] using hz

  refine ⟨f, g, h, hcomm, hhzero, ⟨?_⟩⟩
  exact ShortComplex.isoMk eX eM ePrev hfirst hsecond

section FiniteTauCategory

universe w

variable [HasFiniteBiproducts C] [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

open CategoricalRadical

/-- A split-monic factor of a chosen right mesh map is right minimal, also
after the recorded endpoint isomorphism.
@isnad1 id=isrightm.0h6v.s7.50429dce9414 from=translated src=- shape=5b246cfa vocab=cd402d0b
-/
theorem isRightMinimal_splitFactor_chosen_rightMesh
    (T : FiniteRightTauCategoryData C Ind)
    {Z Y : C} (j : Z ⟶ (T.rightMesh Y).X₂) [IsSplitMono j] :
    IsRightMinimal
      (j ≫ (T.rightMesh Y).g ≫ (T.rightTermIso Y).hom) :=
  by
    simpa only [Category.assoc] using
      IsRightMinimal.postcomp_iso (T.rightTermIso Y)
        ((T.rightTau Y).isRightMinimal_g.precomp_splitMono j)

/-- Every radical-square perturbation of a split-monic chosen-right-mesh
factor is again right minimal.
@isnad1 id=isrightm.1h7v.s8.80ff6f75c4cf from=translated src=- shape=538ad85c vocab=c0abe558
-/
theorem isRightMinimal_add_mem_square_splitFactor_chosen_rightMesh
    (T : FiniteRightTauCategoryData C Ind)
    {Z Y : C} (j : Z ⟶ (T.rightMesh Y).X₂) [IsSplitMono j]
    (r : Z ⟶ Y)
    (hr : r ∈ (T.radical.ideal.pow 2).hom Z Y) :
    IsRightMinimal
      (j ≫ (T.rightMesh Y).g ≫ (T.rightTermIso Y).hom + r) := by
  have hr' :
      r ≫ (T.rightTermIso Y).inv ∈
        (T.radical.ideal.pow 2).hom Z (T.rightMesh Y).X₃ :=
    (T.radical.ideal.pow 2).postcomp (T.rightTermIso Y).inv hr
  obtain ⟨s, hs, hsEq⟩ :=
    (T.rightTau Y).toTauApproximation
      |>.exists_radical_factor_into_of_mem_square T.radical hr'
  have hsRad : IsRadicalMorphism s :=
    (T.radical.mem_ideal_iff s).1 hs
  letI : IsSplitMono (j + s) :=
    isSplitMono_add_of_isRadicalMorphism j hsRad
  have hsum :
      (j + s) ≫ (T.rightMesh Y).g ≫ (T.rightTermIso Y).hom =
        j ≫ (T.rightMesh Y).g ≫ (T.rightTermIso Y).hom + r := by
    rw [Preadditive.add_comp]
    congr 1
    calc
      s ≫ (T.rightMesh Y).g ≫ (T.rightTermIso Y).hom =
          (r ≫ (T.rightTermIso Y).inv) ≫
            (T.rightTermIso Y).hom := by
              simpa only [Category.assoc] using
                congrArg (fun q ↦ q ≫ (T.rightTermIso Y).hom) hsEq
      _ = r := by simp
  rw [← hsum]
  exact isRightMinimal_splitFactor_chosen_rightMesh T (j + s)

/-- The first map of every chosen left mesh is special.  This supplies the
`μ⁻` seed in Iyama's right-ladder existence theorem.
@isnad1 id=isspecia.0h4v.s6.12331fcfdc2d from=translated src=- shape=95e7d7ae vocab=34d2be3f
-/
theorem isSpecial_leftMesh_f
    (T : FiniteTauCategoryData C Ind) (A : C) :
    IsSpecial T.radical (T.leftMesh A).f :=
  (T.leftTau A).isSpecial_f T.radical

/-- Every radical arrow into `Y` factors through the second map of the chosen
right mesh at `Y`, after applying the recorded right-endpoint isomorphism.

This is the first operation in the special-arrow construction.  It follows
directly from the radical approximation field of the chosen right
tau-sequence; no Krull--Schmidt decomposition is involved yet.
@isnad1 id=ex.1h6v.s7.de403bdc94b6 from=translated src=- shape=469d44c4 vocab=12ecd969
-/
theorem exists_factor_through_chosen_rightMesh
    (T : FiniteRightTauCategoryData C Ind)
    {X Y : C} (a : X ⟶ Y) (ha : IsRadicalMorphism a) :
    ∃ k : X ⟶ (T.rightMesh Y).X₂,
      k ≫ (T.rightMesh Y).g ≫ (T.rightTermIso Y).hom = a := by
  have ha' :
      IsRadicalMorphism (a ≫ (T.rightTermIso Y).inv) :=
    isRadicalMorphism_postcomp (T.rightTermIso Y).inv ha
  obtain ⟨k, hk⟩ :=
    (T.rightTau Y).factors_into_right
      (a ≫ (T.rightTermIso Y).inv) ha'
  refine ⟨k, ?_⟩
  calc
    k ≫ (T.rightMesh Y).g ≫ (T.rightTermIso Y).hom =
        (k ≫ (T.rightMesh Y).g) ≫ (T.rightTermIso Y).hom :=
      (Category.assoc _ _ _).symm
    _ = (a ≫ (T.rightTermIso Y).inv) ≫
        (T.rightTermIso Y).hom := by rw [hk]
    _ = a := by simp

/-- Chosen-right-mesh specialization of the invariant one-step theorem.

Once `j` is the split-monic essential factor of the current arrow and the
raw successor is displayed as `(bNext, 0)`, idempotent completeness supplies
the complement and hence the entire explicit right-ladder step.
@isnad1 id=other.1h12v.s10.802619272974 from=translated src=- shape=a018cf6b vocab=c31052c1
-/
theorem exists_chosen_rightMesh_step_of_split_factor_and_padded_next
    (T : FiniteRightTauCategoryData C Ind)
    {YPrev ZPrev ZNext YNext U : C}
    (j : ZPrev ⟶ (T.rightMesh YPrev).X₂) [IsSplitMono j]
    (bNext : ZNext ⟶ YNext)
    (eX : (T.rightMesh YPrev).X₁ ≅ ZNext ⊞ U)
    (eY : (splitMonoComplement j).complement ≅ YNext)
    (heNext :
      ((T.rightMesh YPrev).f ≫
          (splitMonoComplement j).projection) ≫ eY.hom =
        eX.hom ≫ biprod.desc bNext (0 : U ⟶ YNext)) :
    let bPrev : ZPrev ⟶ YPrev :=
      j ≫ (T.rightMesh YPrev).g ≫ (T.rightTermIso YPrev).hom
    ∃ (f : YNext ⟶ YPrev) (g : ZNext ⟶ ZPrev)
      (h : U ⟶ ZPrev)
      (comm : bNext ≫ f = g ≫ bPrev)
      (hzero : h ≫ bPrev = 0),
        Nonempty
          (T.rightMesh YPrev ≅
            stepComplex bPrev bNext f g h comm hzero) := by
  exact exists_stepComplex_iso_of_split_factor_and_padded_next
    (T.rightMesh YPrev) (T.rightTermIso YPrev) j
      (splitMonoComplement j) bNext eX eY heNext

end FiniteTauCategory

end QuotientSubmoduleEquidistribution.Iyama.RightLadder
