/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Tengoku.AclGeom.AclGeom.Correspondence.FiniteCover
import Tengoku.AclGeom.AclGeom.Correspondence.GroupConfiguration
import Tengoku.Seed.CategoryTheory.Action

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The groupoid of conjugate branches on a normal cover

A finite selected correspondence becomes single-valued only after choosing
one embedding of its branch field into a common normal cover.  The deck
transformation group of that cover acts on all such embeddings by
postcomposition.  Its action groupoid is the precise categorical object
which records the selected branch and all of its conjugates:

* `NormalBranchEmbedding` wraps an embedding of the branch field into the
  normal cover;
* deck transformations act by postcomposition;
* normality makes this action transitive, since every branch embedding
  extends to an automorphism of the normal cover;
* `normalBranchGroupoid` is therefore a connected genuine groupoid;
* every chosen arrow family in it carries the rational group chunk supplied
  by `groupoidArrowChunk`.

This construction resolves the finite branch ambiguity on a fixed normal
cover.  The separate geometric task is to assemble the varying generic
parameter families into the normal covers used here.

This module is part of the finite-cover integration in blueprint §8.1.
-/

namespace AclGeom

noncomputable section

open CategoryTheory

section NormalBranchAction

variable (E M N : Type*) [Field E] [Field M] [Field N]
  [Algebra E M] [Algebra E N]

/-- An embedding of a selected branch field `M` into a normal cover `N`,
over the endpoint field `E`.-/
@[ext]
structure NormalBranchEmbedding where
  /-- The underlying embedding of function fields.-/
  toAlgHom : M →ₐ[E] N

namespace NormalBranchEmbedding

variable {E M N}

section Reparametrize

variable {M' : Type*} [Field M'] [Algebra E M']

/-- Regard an embedding of an equivalent branch field as an embedding of
the original branch field.  This is the domain-side operation needed before
two selected branches can be compared by a deck transformation of one
normal cover.-/
def reparametrize (g : NormalBranchEmbedding E M' N)
    (e : M ≃ₐ[E] M') : NormalBranchEmbedding E M N :=
  ⟨g.toAlgHom.comp e.toAlgHom⟩

/--
@isnad1 id=eq.0h7v.s8.cc78ad50e839 from=translated src=- shape=8e78d6c2 vocab=298207f5
-/
@[simp] theorem reparametrize_apply
    (g : NormalBranchEmbedding E M' N) (e : M ≃ₐ[E] M') (x : M) :
    (g.reparametrize e).toAlgHom x = g.toAlgHom (e x) :=
  rfl

end Reparametrize

section Transport

variable {E' M' N' : Type*} [Field E'] [Field M'] [Field N']
  [Algebra E' M'] [Algebra E' N']

/-- Transport a branch embedding along compatible equivalences of its
base, branch field, and normal-cover field.-/
def mapOfEquiv (eE : E ≃+* E') (eM : M ≃+* M') (eN : N ≃+* N')
    (hM : eM.toRingHom.comp (algebraMap E M) =
      (algebraMap E' M').comp eE.toRingHom)
    (hN : eN.toRingHom.comp (algebraMap E N) =
      (algebraMap E' N').comp eE.toRingHom)
    (f : NormalBranchEmbedding E M N) :
    NormalBranchEmbedding E' M' N' := by
  have hM_symm (x : E') :
      eM.symm (algebraMap E' M' x) =
        algebraMap E M (eE.symm x) := by
    apply eM.injective
    rw [eM.apply_symm_apply]
    have hm := DFunLike.congr_fun hM (eE.symm x)
    change eM (algebraMap E M (eE.symm x)) =
      algebraMap E' M' (eE (eE.symm x)) at hm
    rw [eE.apply_symm_apply] at hm
    exact hm.symm
  refine ⟨{
    toRingHom := (eN.toRingHom.comp f.toAlgHom.toRingHom).comp
      eM.symm.toRingHom
    commutes' := fun x ↦ ?_ }⟩
  change eN (f.toAlgHom (eM.symm (algebraMap E' M' x))) =
    algebraMap E' N' x
  rw [hM_symm, f.toAlgHom.commutes]
  have hn := DFunLike.congr_fun hN (eE.symm x)
  change eN (algebraMap E N (eE.symm x)) =
    algebraMap E' N' (eE (eE.symm x)) at hn
  rwa [eE.apply_symm_apply] at hn

/-- Transport of branch embeddings is pointwise conjugation by the branch-
and normal-field equivalences.
@isnad1 id=eq.2h11v.s10.b55d4f4b96f7 from=translated src=- shape=ad6073e8 vocab=518e528e
-/
@[simp] theorem mapOfEquiv_apply
    (eE : E ≃+* E') (eM : M ≃+* M') (eN : N ≃+* N')
    (hM : eM.toRingHom.comp (algebraMap E M) =
      (algebraMap E' M').comp eE.toRingHom)
    (hN : eN.toRingHom.comp (algebraMap E N) =
      (algebraMap E' N').comp eE.toRingHom)
    (f : NormalBranchEmbedding E M N) (x : M') :
    (mapOfEquiv eE eM eN hM hN f).toAlgHom x =
      eN (f.toAlgHom (eM.symm x)) := by
  change eN (f.toAlgHom (eM.symm x)) = _
  rfl

/-- Compatible field equivalences induce an equivalence of the corresponding
types of conjugate branches.-/
def equivOfEquiv (eE : E ≃+* E') (eM : M ≃+* M') (eN : N ≃+* N')
    (hM : eM.toRingHom.comp (algebraMap E M) =
      (algebraMap E' M').comp eE.toRingHom)
    (hN : eN.toRingHom.comp (algebraMap E N) =
      (algebraMap E' N').comp eE.toRingHom) :
    NormalBranchEmbedding E M N ≃ NormalBranchEmbedding E' M' N' := by
  have hM' : eM.symm.toRingHom.comp (algebraMap E' M') =
      (algebraMap E M).comp eE.symm.toRingHom := by
    apply RingHom.ext
    intro x
    change eM.symm (algebraMap E' M' x) =
      algebraMap E M (eE.symm x)
    apply eM.injective
    rw [eM.apply_symm_apply]
    have hm := DFunLike.congr_fun hM (eE.symm x)
    change eM (algebraMap E M (eE.symm x)) =
      algebraMap E' M' (eE (eE.symm x)) at hm
    rw [eE.apply_symm_apply] at hm
    exact hm.symm
  have hN' : eN.symm.toRingHom.comp (algebraMap E' N') =
      (algebraMap E N).comp eE.symm.toRingHom := by
    apply RingHom.ext
    intro x
    change eN.symm (algebraMap E' N' x) =
      algebraMap E N (eE.symm x)
    apply eN.injective
    rw [eN.apply_symm_apply]
    have hn := DFunLike.congr_fun hN (eE.symm x)
    change eN (algebraMap E N (eE.symm x)) =
      algebraMap E' N' (eE (eE.symm x)) at hn
    rw [eE.apply_symm_apply] at hn
    exact hn.symm
  exact
    { toFun := mapOfEquiv eE eM eN hM hN
      invFun := mapOfEquiv eE.symm eM.symm eN.symm hM' hN'
      left_inv := fun f ↦ by
        ext x
        simp
      right_inv := fun f ↦ by
        ext x
        simp }

/-- Conjugation by a semilinear equivalence of normal-cover fields
transports deck transformations between the two base fields.-/
def deckMapOfEquiv (eE : E ≃+* E') (eN : N ≃+* N')
    (hN : eN.toRingHom.comp (algebraMap E N) =
      (algebraMap E' N').comp eE.toRingHom)
    (σ : N ≃ₐ[E] N) : N' ≃ₐ[E'] N' := by
  let r : N' ≃+* N' := eN.symm.trans (σ.toRingEquiv.trans eN)
  apply AlgEquiv.ofRingEquiv (f := r)
  intro x
  change eN (σ (eN.symm (algebraMap E' N' x))) =
    algebraMap E' N' x
  have hN_symm :
      eN.symm (algebraMap E' N' x) =
        algebraMap E N (eE.symm x) := by
    apply eN.injective
    rw [eN.apply_symm_apply]
    have hn := DFunLike.congr_fun hN (eE.symm x)
    change eN (algebraMap E N (eE.symm x)) =
      algebraMap E' N' (eE (eE.symm x)) at hn
    rw [eE.apply_symm_apply] at hn
    exact hn.symm
  rw [hN_symm, σ.commutes]
  have hn := DFunLike.congr_fun hN (eE.symm x)
  change eN (algebraMap E N (eE.symm x)) =
    algebraMap E' N' (eE (eE.symm x)) at hn
  rwa [eE.apply_symm_apply] at hn

/-- Deck transport acts by conjugation on the underlying normal-cover
field.
@isnad1 id=eq.1h8v.s9.a6e93b849d2e from=translated src=- shape=61c8c40c vocab=6740e253
-/
@[simp] theorem deckMapOfEquiv_apply
    (eE : E ≃+* E') (eN : N ≃+* N')
    (hN : eN.toRingHom.comp (algebraMap E N) =
      (algebraMap E' N').comp eE.toRingHom)
    (σ : N ≃ₐ[E] N) (x : N') :
    deckMapOfEquiv eE eN hN σ x = eN (σ (eN.symm x)) := by
  rfl

/-- A compatible equivalence of normal-cover fields identifies their
deck-transformation groups.-/
def deckEquivOfEquiv (eE : E ≃+* E') (eN : N ≃+* N')
    (hN : eN.toRingHom.comp (algebraMap E N) =
      (algebraMap E' N').comp eE.toRingHom) :
    (N ≃ₐ[E] N) ≃* (N' ≃ₐ[E'] N') := by
  have hN' : eN.symm.toRingHom.comp (algebraMap E' N') =
      (algebraMap E N).comp eE.symm.toRingHom := by
    apply RingHom.ext
    intro x
    change eN.symm (algebraMap E' N' x) =
      algebraMap E N (eE.symm x)
    apply eN.injective
    rw [eN.apply_symm_apply]
    have hn := DFunLike.congr_fun hN (eE.symm x)
    change eN (algebraMap E N (eE.symm x)) =
      algebraMap E' N' (eE (eE.symm x)) at hn
    rw [eE.apply_symm_apply] at hn
    exact hn.symm
  exact
    { toFun := deckMapOfEquiv eE eN hN
      invFun := deckMapOfEquiv eE.symm eN.symm hN'
      left_inv := fun σ ↦ by
        ext x
        simp
      right_inv := fun σ ↦ by
        ext x
        simp
      map_mul' := fun σ τ ↦ by
        ext x
        simp [AlgEquiv.mul_apply] }

end Transport

/-- A deck transformation acts on a branch embedding by
postcomposition.-/
instance : SMul (N ≃ₐ[E] N) (NormalBranchEmbedding E M N) where
  smul σ f := ⟨σ.toAlgHom.comp f.toAlgHom⟩

/--
@isnad1 id=eq.0h5v.s8.6553da1a4326 from=translated src=- shape=5b18103f vocab=48b599c8
-/
@[simp] theorem smul_toAlgHom (σ : N ≃ₐ[E] N)
    (f : NormalBranchEmbedding E M N) :
    (σ • f).toAlgHom = σ.toAlgHom.comp f.toAlgHom := rfl

/-- Postcomposition is a genuine action of the deck-transformation
group.-/
instance : MulAction (N ≃ₐ[E] N) (NormalBranchEmbedding E M N) where
  one_smul f := by
    ext x
    rfl
  mul_smul σ τ f := by
    ext x
    rfl

section TransportAction

variable {E' M' N' : Type*} [Field E'] [Field M'] [Field N']
  [Algebra E' M'] [Algebra E' N']

/-- Branch transport is equivariant for conjugation transport of deck
transformations.
@isnad1 id=eq.2h11v.s9.feb1768aee82 from=translated src=- shape=30e4dbc3 vocab=ffbfab18
-/
@[simp] theorem mapOfEquiv_smul
    (eE : E ≃+* E') (eM : M ≃+* M') (eN : N ≃+* N')
    (hM : eM.toRingHom.comp (algebraMap E M) =
      (algebraMap E' M').comp eE.toRingHom)
    (hN : eN.toRingHom.comp (algebraMap E N) =
      (algebraMap E' N').comp eE.toRingHom)
    (σ : N ≃ₐ[E] N) (f : NormalBranchEmbedding E M N) :
    mapOfEquiv eE eM eN hM hN (σ • f) =
      deckMapOfEquiv eE eN hN σ •
        mapOfEquiv eE eM eN hM hN f := by
  ext x
  simp

end TransportAction

variable [Algebra M N] [IsScalarTower E M N]

/-- The literal inclusion of the branch field in its cover.-/
def canonical : NormalBranchEmbedding E M N :=
  ⟨IsScalarTower.toAlgHom E M N⟩

/--
@isnad1 id=eq.0h4v.s8.b5e8c5e37bab from=translated src=- shape=c4cbf6da vocab=1a4e80e0
-/
@[simp] theorem canonical_apply (x : M) :
    (canonical (E := E) (M := M) (N := N)).toAlgHom x =
      algebraMap M N x := rfl

/-- Normality extends any branch embedding to a deck transformation.-/
def extendToAut [Normal E N] (f : NormalBranchEmbedding E M N) :
    N ≃ₐ[E] N :=
  AlgEquiv.ofBijective (f.toAlgHom.liftNormal N)
    (AlgHom.normal_bijective E N N _)

/-- The extended deck transformation sends the literal branch to the
chosen conjugate branch.
@isnad1 id=eq.0h4v.s8.264976016c0f from=translated src=- shape=364e6b3c vocab=1af8bf82
-/
theorem extendToAut_smul_canonical [Normal E N]
    (f : NormalBranchEmbedding E M N) :
    f.extendToAut • canonical (E := E) (M := M) (N := N) = f := by
  ext x
  exact f.toAlgHom.liftNormal_commutes N x

end NormalBranchEmbedding

namespace NormalBranchEmbedding

variable {E M N}

/-- The distinguished deck transformation carrying one branch embedding
to another.  The first embedding supplies the temporary algebra structure
on the branch field, so this definition does not depend on an unrelated
ambient inclusion of that field into the normal cover.-/
noncomputable def alignmentAut [Normal E N]
    (f g : NormalBranchEmbedding E M N) : N ≃ₐ[E] N := by
  letI : Algebra M N := f.toAlgHom.toAlgebra
  letI : IsScalarTower E M N :=
    IsScalarTower.of_algebraMap_eq fun x ↦ f.toAlgHom.commutes x |>.symm
  exact g.extendToAut

/-- The distinguished alignment automorphism sends its anchoring branch
embedding to the requested branch embedding.
@isnad1 id=eq.0h5v.s7.328c24034446 from=translated src=- shape=8cc9dd15 vocab=5ba88416
-/
theorem alignmentAut_smul [Normal E N]
    (f g : NormalBranchEmbedding E M N) :
    alignmentAut f g • f = g := by
  letI : Algebra M N := f.toAlgHom.toAlgebra
  letI : IsScalarTower E M N :=
    IsScalarTower.of_algebraMap_eq fun x ↦ f.toAlgHom.commutes x |>.symm
  exact g.extendToAut_smul_canonical

/-- Extend a prescribed automorphism of an embedded finite branch field to
an automorphism of the ambient normal cover.  This is the subcover-chart
operation: `f` fixes the chosen copy of the smaller cover and `e` prescribes
the chart on that copy.-/
noncomputable def extendAlong [Normal E N]
    (f : M →ₐ[E] N) (e : M ≃ₐ[E] M) : N ≃ₐ[E] N :=
  alignmentAut ⟨f⟩ ⟨f.comp e.toAlgHom⟩

/-- The extended normal-cover chart has exactly the prescribed action on
the embedded branch field.
@isnad1 id=eq.0h6v.s8.2fb57e7005f9 from=translated src=- shape=f37463e9 vocab=22154037
-/
@[simp] theorem extendAlong_apply [Normal E N]
    (f : M →ₐ[E] N) (e : M ≃ₐ[E] M) (x : M) :
    extendAlong f e (f x) = f (e x) := by
  have h := congrArg (fun b : NormalBranchEmbedding E M N ↦ b.toAlgHom x)
    (alignmentAut_smul (⟨f⟩ : NormalBranchEmbedding E M N)
      ⟨f.comp e.toAlgHom⟩)
  exact h

/-- The deck-transformation action on branches of a normal cover is
transitive.
@isnad1 id=ex.0h5v.s7.5b403ebab628 from=translated src=- shape=db0adfbe vocab=bb6dcea3
-/
theorem exists_smul_eq [Normal E N]
    (f g : NormalBranchEmbedding E M N) :
    ∃ σ : N ≃ₐ[E] N, σ • f = g := by
  exact ⟨alignmentAut f g, alignmentAut_smul f g⟩

end NormalBranchEmbedding

section ActionCategoryTransport

variable {G H X Y : Type*} [Group G] [Group H]
  [MulAction G X] [MulAction H Y]

/-- Left multiplication by a group element as an equivalence of the
underlying action.-/
def mulActionEquiv (g : G) : X ≃ X where
  toFun := (g • ·)
  invFun := (g⁻¹ • ·)
  left_inv x := by simp
  right_inv x := by simp

/--
@isnad1 id=eq.0h4v.s6.4bd95d297ccd from=translated src=- shape=ca5fc98a vocab=c2b5ce1b
-/
@[simp] theorem mulActionEquiv_apply (g : G) (x : X) :
    mulActionEquiv g x = g • x := rfl

end ActionCategoryTransport

section ActionCategoryTranslationChunk

variable {E N X : Type*} [Field E] [Field N] [Algebra E N]
  [MulAction (N ≃ₐ[E] N) X]
  {x y : ActionCategory (N ≃ₐ[E] N) X}

end ActionCategoryTranslationChunk

/-- The action groupoid of conjugate embeddings of a branch field into a
normal cover.-/
abbrev normalBranchGroupoid :=
  ActionCategory (N ≃ₐ[E] N) (NormalBranchEmbedding E M N)

namespace normalBranchGroupoid

variable {E M N} [Algebra M N] [IsScalarTower E M N]

/-- The object represented by the literal inclusion of the branch field.-/
def selectedObject : normalBranchGroupoid E M N :=
  NormalBranchEmbedding.canonical (E := E) (M := M) (N := N)

/-- The object represented by a chosen conjugate branch.-/
def object (f : NormalBranchEmbedding E M N) :
    normalBranchGroupoid E M N := f

/-- The canonical arrow from the selected branch to any conjugate branch,
labelled by the normal extension of that branch embedding.-/
def selectedArrow [Normal E N] (f : NormalBranchEmbedding E M N) :
    selectedObject (E := E) (M := M) (N := N) ⟶ object f :=
  ⟨f.extendToAut, f.extendToAut_smul_canonical⟩

/-- Every based conjugate-branch arrow family on the normal cover carries
the rational group chunk transported from the genuine action groupoid.-/
def arrowChunk [Normal E N] (f : NormalBranchEmbedding E M N) :
    RationalGroupChunk
      (selectedObject (E := E) (M := M) (N := N) ⟶ object f) :=
  groupoidArrowChunk (selectedArrow f)

end normalBranchGroupoid

end NormalBranchAction

section FiniteCoverBranches

open IntermediateField

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
  {E L : IntermediateField k Ω}

/-- Branch embeddings of a concrete finite cover into its normal closure.-/
abbrev FiniteCoverBranch (h : E ≤ L) :=
  NormalBranchEmbedding (↥E) (↥(extendScalars h))
    (↥(FiniteCover.normalClosureOver h))

/-- Deck transformations of a concrete finite normal cover.-/
abbrev FiniteCoverDeck (h : E ≤ L) :=
  (↥(FiniteCover.normalClosureOver h)) ≃ₐ[↥E]
    (↥(FiniteCover.normalClosureOver h))

/-- A compatible equivalence of selected finite extensions and their
concrete normal-cover fields transports the corresponding branch types.-/
def finiteCoverBranchEquivOfExtensionEquiv
    {E' L' : IntermediateField k Ω} (h : E ≤ L) (h' : E' ≤ L')
    (e : FiniteCover.ExtensionEquiv h h')
    (n : (↥(FiniteCover.normalClosureOver h)) ≃+*
      (↥(FiniteCover.normalClosureOver h')))
    (hn : n.toRingHom.comp
        (algebraMap (↥E) (↥(FiniteCover.normalClosureOver h))) =
      (algebraMap (↥E') (↥(FiniteCover.normalClosureOver h'))).comp
        e.baseEquiv.toRingEquiv.toRingHom) :
    FiniteCoverBranch h ≃ FiniteCoverBranch h' := by
  let eM : (↥(extendScalars h)) ≃+* (↥(extendScalars h')) :=
    e.totalEquiv.toRingEquiv
  apply NormalBranchEmbedding.equivOfEquiv
    e.baseEquiv.toRingEquiv eM n
  · apply RingHom.ext
    intro x
    exact e.commutes_apply x
  · exact hn

/-- The same compatible normal-cover equivalence transports deck
transformations by conjugation.-/
def finiteCoverDeckEquivOfExtensionEquiv
    {E' L' : IntermediateField k Ω} (h : E ≤ L) (h' : E' ≤ L')
    (e : FiniteCover.ExtensionEquiv h h')
    (n : (↥(FiniteCover.normalClosureOver h)) ≃+*
      (↥(FiniteCover.normalClosureOver h')))
    (hn : n.toRingHom.comp
        (algebraMap (↥E) (↥(FiniteCover.normalClosureOver h))) =
      (algebraMap (↥E') (↥(FiniteCover.normalClosureOver h'))).comp
        e.baseEquiv.toRingEquiv.toRingHom) :
    FiniteCoverDeck h ≃* FiniteCoverDeck h' :=
  NormalBranchEmbedding.deckEquivOfEquiv
    e.baseEquiv.toRingEquiv n hn

/-- Branch transport is equivariant for the corresponding transport of
deck transformations.
@isnad1 id=eq.3h10v.s14.b4bd31f39f99 from=translated src=- shape=57690b47 vocab=25080936
-/
@[simp] theorem finiteCoverBranchEquivOfExtensionEquiv_smul
    {E' L' : IntermediateField k Ω} (h : E ≤ L) (h' : E' ≤ L')
    (e : FiniteCover.ExtensionEquiv h h')
    (n : (↥(FiniteCover.normalClosureOver h)) ≃+*
      (↥(FiniteCover.normalClosureOver h')))
    (hn : n.toRingHom.comp
        (algebraMap (↥E) (↥(FiniteCover.normalClosureOver h))) =
      (algebraMap (↥E') (↥(FiniteCover.normalClosureOver h'))).comp
        e.baseEquiv.toRingEquiv.toRingHom)
    (σ : FiniteCoverDeck h) (b : FiniteCoverBranch h) :
    finiteCoverBranchEquivOfExtensionEquiv h h' e n hn (σ • b) =
      finiteCoverDeckEquivOfExtensionEquiv h h' e n hn σ •
        finiteCoverBranchEquivOfExtensionEquiv h h' e n hn b := by
  unfold finiteCoverBranchEquivOfExtensionEquiv
    finiteCoverDeckEquivOfExtensionEquiv
    NormalBranchEmbedding.equivOfEquiv
    NormalBranchEmbedding.deckEquivOfEquiv
  ext x
  simp
  change n ((σ • b).toAlgHom (e.totalEquiv.toRingEquiv.symm x)) =
    n (σ (n.symm (n (b.toAlgHom (e.totalEquiv.toRingEquiv.symm x)))))
  rw [n.symm_apply_apply]
  rfl

/-- The genuine action groupoid of all conjugate branches of a concrete
finite cover.-/
abbrev finiteCoverBranchGroupoid (h : E ≤ L) :=
  normalBranchGroupoid (↥E) (↥(extendScalars h))
    (↥(FiniteCover.normalClosureOver h))

/-- The literal selected branch, regarded as an object of the normal-cover
branch action.-/
def finiteCoverSelectedBranch (h : E ≤ L) : FiniteCoverBranch h :=
  ⟨FiniteCover.selectedEmbedding h⟩

/-- The literal selected branch inside the canonical normal-closure model.
Unlike an arbitrary equivalence between normal closures, this embedding is
the algebra map used in the definition of the canonical normal closure.-/
def finiteCoverCanonicalSelectedBranch [IsAlgClosed Ω] (h : E ≤ L)
    (halg : Algebra.IsAlgebraic (↥E) (↥(extendScalars h))) :
    NormalBranchEmbedding (↥E) (↥(extendScalars h))
      (↥(FiniteCover.canonicalNormalClosure h)) :=
  ⟨FiniteCover.canonicalSelectedEmbedding h halg⟩

/-- Place the distinguished canonical branch in any larger canonical
source cover which contains its normal closure.-/
def finiteCoverCanonicalSelectedBranchIn
    [IsAlgClosed Ω] (h : E ≤ L)
    (halg : Algebra.IsAlgebraic (↥E) (↥(extendScalars h)))
    (N : IntermediateField (↥E) (AlgebraicClosure (↥E)))
    (hle : FiniteCover.canonicalNormalClosure h ≤ N) :
    NormalBranchEmbedding (↥E) (↥(extendScalars h)) (↥N) :=
  ⟨(IntermediateField.inclusion hle).comp
    (FiniteCover.canonicalSelectedEmbedding h halg)⟩

/-- The selected branch as an object of its conjugate-branch groupoid.-/
def finiteCoverSelectedObject (h : E ≤ L) :
    finiteCoverBranchGroupoid h :=
  finiteCoverSelectedBranch h

/-- An equivalence of finite-cover branch actions which additionally
preserves the literal selected branch.-/
structure FiniteCoverBasedBranchEquiv
    {E' L' : IntermediateField k Ω} (h : E ≤ L) (h' : E' ≤ L') where
  /-- The induced equivalence of deck-transformation groups.-/
  deckEquiv : FiniteCoverDeck h ≃* FiniteCoverDeck h'
  /-- The induced equivalence of conjugate branch types.-/
  branchEquiv : FiniteCoverBranch h ≃ FiniteCoverBranch h'
  /-- Deck actions and branch transport commute.-/
  map_smul : ∀ σ b,
    branchEquiv (σ • b) = deckEquiv σ • branchEquiv b
  /-- The literal selected branch is preserved.-/
  map_selected :
    branchEquiv (finiteCoverSelectedBranch h) =
      finiteCoverSelectedBranch h'

/-- Inside an algebraically closed ambient field, deck transformations act
transitively on the conjugate branches of a finite cover.
@isnad1 id=ex.2h6v.s10.370af3a30d38 from=translated src=- shape=c4940288 vocab=5c9621c8
-/
theorem finiteCoverBranch_exists_smul_eq [IsAlgClosed Ω]
    (h : E ≤ L)
    (hfin : FiniteDimensional (↥E) (↥(extendScalars h)))
    (f g : FiniteCoverBranch h) :
    ∃ σ : FiniteCoverDeck h, σ • f = g := by
  letI : Algebra (↥(extendScalars h))
      (↥(FiniteCover.normalClosureOver h)) :=
    (FiniteCover.selectedEmbedding h).toAlgebra
  letI : IsScalarTower (↥E) (↥(extendScalars h))
      (↥(FiniteCover.normalClosureOver h)) :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      (FiniteCover.selectedEmbedding h).commutes x |>.symm
  letI : FiniteDimensional (↥E) (↥(extendScalars h)) := hfin
  letI : Normal (↥E) (↥(FiniteCover.normalClosureOver h)) :=
    FiniteCover.normalClosureOver_normal h
      (Algebra.IsAlgebraic.of_finite (↥E) (↥(extendScalars h)))
  exact NormalBranchEmbedding.exists_smul_eq f g

/-- A semilinear equivalence of concrete normal-cover fields which preserves
the literal selected finite-extension branch.  The base and total
equivalences are retained explicitly so the selected-branch equation can be
evaluated on named coordinates after transport.-/
structure FiniteCoverBasedNormalEquiv
    {E' L' : IntermediateField k Ω} (h : E ≤ L) (h' : E' ≤ L')
    (e : FiniteCover.ExtensionEquiv h h') where
  /-- The selected-branch-preserving equivalence of normal-cover fields.-/
  toRingEquiv :
    (↥(FiniteCover.normalClosureOver h)) ≃+*
      (↥(FiniteCover.normalClosureOver h'))
  /-- The normal-cover equivalence is semilinear over the displayed base
  equivalence.-/
  commutes :
    toRingEquiv.toRingHom.comp
        (algebraMap (↥E) (↥(FiniteCover.normalClosureOver h))) =
      (algebraMap (↥E') (↥(FiniteCover.normalClosureOver h'))).comp
        e.baseEquiv.toRingEquiv.toRingHom
  /-- The corrected normal-cover equivalence carries the literal selected
  branch to the literal selected target branch through the total-field
  equivalence.-/
  map_selected :
    toRingEquiv.toRingHom.comp
        (FiniteCover.selectedEmbedding h).toRingHom =
      (FiniteCover.selectedEmbedding h').toRingHom.comp
        e.totalEquiv.toRingEquiv.toRingHom

namespace FiniteCoverBasedNormalEquiv

variable {E' L' : IntermediateField k Ω} {h : E ≤ L} {h' : E' ≤ L'}
  {e : FiniteCover.ExtensionEquiv h h'}

/-- Pointwise form of the selected-branch preservation equation.
@isnad1 id=eq.2h9v.s14.05f71a44aafa from=translated src=- shape=da29ef06 vocab=8babc251
-/
@[simp] theorem map_selected_apply (T : FiniteCoverBasedNormalEquiv h h' e)
    (x : extendScalars h) :
    T.toRingEquiv (FiniteCover.selectedEmbedding h x) =
      FiniteCover.selectedEmbedding h' (e.totalEquiv x) :=
  DFunLike.congr_fun T.map_selected x

/-- A based normal-cover equivalence induces the corresponding equivalence
of based conjugate-branch actions, without making any further branch
choice.-/
def toBasedBranchEquiv (T : FiniteCoverBasedNormalEquiv h h' e) :
    FiniteCoverBasedBranchEquiv h h' := by
  let branchEquiv := finiteCoverBranchEquivOfExtensionEquiv
    h h' e T.toRingEquiv T.commutes
  let deckEquiv := finiteCoverDeckEquivOfExtensionEquiv
    h h' e T.toRingEquiv T.commutes
  refine
    { deckEquiv := deckEquiv
      branchEquiv := branchEquiv
      map_smul := fun σ b ↦ ?_
      map_selected := ?_ }
  · exact finiteCoverBranchEquivOfExtensionEquiv_smul
      h h' e T.toRingEquiv T.commutes σ b
  · apply NormalBranchEmbedding.ext
    apply AlgHom.ext
    intro y
    have hy := T.map_selected_apply (e.totalEquiv.symm y)
    change T.toRingEquiv
        (FiniteCover.selectedEmbedding h (e.totalEquiv.symm y)) =
      FiniteCover.selectedEmbedding h' y
    exact hy.trans (congrArg (FiniteCover.selectedEmbedding h')
      (e.totalEquiv.apply_symm_apply y))

end FiniteCoverBasedNormalEquiv

/-- A transported normal cover can be based at the literal target branch:
transitivity supplies a target deck transformation correcting the raw
field-theoretic equivalence.  The corrected field equivalence remains
semilinear over the original base equivalence and now carries the entire
literal selected branch through the displayed total-field equivalence.-/
noncomputable def finiteCoverBasedNormalEquivOfExtensionEquiv [IsAlgClosed Ω]
    {E' L' : IntermediateField k Ω} (h : E ≤ L) (h' : E' ≤ L')
    (hfin' : FiniteDimensional (↥E') (↥(extendScalars h')))
    (e : FiniteCover.ExtensionEquiv h h')
    (n : (↥(FiniteCover.normalClosureOver h)) ≃+*
      (↥(FiniteCover.normalClosureOver h')))
    (hn : n.toRingHom.comp
        (algebraMap (↥E) (↥(FiniteCover.normalClosureOver h))) =
      (algebraMap (↥E') (↥(FiniteCover.normalClosureOver h'))).comp
        e.baseEquiv.toRingEquiv.toRingHom) :
    FiniteCoverBasedNormalEquiv h h' e := by
  let rawBranch := finiteCoverBranchEquivOfExtensionEquiv h h' e n hn
  let hex := finiteCoverBranch_exists_smul_eq h' hfin'
    (rawBranch (finiteCoverSelectedBranch h))
    (finiteCoverSelectedBranch h')
  let τ : FiniteCoverDeck h' := Classical.choose hex
  have hτ : τ • rawBranch (finiteCoverSelectedBranch h) =
      finiteCoverSelectedBranch h' := Classical.choose_spec hex
  refine
    { toRingEquiv := n.trans τ.toRingEquiv
      commutes := ?_
      map_selected := ?_ }
  · apply RingHom.ext
    intro x
    have hx := DFunLike.congr_fun hn x
    change n (algebraMap (↥E)
        (↥(FiniteCover.normalClosureOver h)) x) =
      algebraMap (↥E') (↥(FiniteCover.normalClosureOver h'))
        (e.baseEquiv x) at hx
    change τ (n (algebraMap (↥E)
        (↥(FiniteCover.normalClosureOver h)) x)) =
      algebraMap (↥E') (↥(FiniteCover.normalClosureOver h'))
        (e.baseEquiv x)
    rw [hx]
    exact τ.commutes (e.baseEquiv x)
  · apply RingHom.ext
    intro x
    have hx := congrArg (fun f ↦ f.toAlgHom (e.totalEquiv x)) hτ
    change τ (n (FiniteCover.selectedEmbedding h
        (e.totalEquiv.symm (e.totalEquiv x)))) =
      FiniteCover.selectedEmbedding h' (e.totalEquiv x) at hx
    change τ (n (FiniteCover.selectedEmbedding h x)) =
      FiniteCover.selectedEmbedding h' (e.totalEquiv x)
    exact (congrArg (fun z ↦ τ (n (FiniteCover.selectedEmbedding h z)))
      (e.totalEquiv.symm_apply_apply x)).symm.trans hx

/-- Forgetting the corrected field equivalence recovers a selected-branch-
preserving equivalence of the corresponding conjugate-branch actions.-/
noncomputable def finiteCoverBasedBranchEquivOfExtensionEquiv [IsAlgClosed Ω]
    {E' L' : IntermediateField k Ω} (h : E ≤ L) (h' : E' ≤ L')
    (hfin' : FiniteDimensional (↥E') (↥(extendScalars h')))
    (e : FiniteCover.ExtensionEquiv h h')
    (n : (↥(FiniteCover.normalClosureOver h)) ≃+*
      (↥(FiniteCover.normalClosureOver h')))
    (hn : n.toRingHom.comp
        (algebraMap (↥E) (↥(FiniteCover.normalClosureOver h))) =
      (algebraMap (↥E') (↥(FiniteCover.normalClosureOver h'))).comp
        e.baseEquiv.toRingEquiv.toRingHom) :
    FiniteCoverBasedBranchEquiv h h' :=
  (finiteCoverBasedNormalEquivOfExtensionEquiv
    h h' hfin' e n hn).toBasedBranchEquiv

namespace FiniteCoverBasedBranchEquiv

variable {E' L' : IntermediateField k Ω} {h : E ≤ L} {h' : E' ≤ L'}

/-- Identity transport of a based finite-cover branch action.-/
def refl (h : E ≤ L) : FiniteCoverBasedBranchEquiv h h where
  deckEquiv := MulEquiv.refl _
  branchEquiv := Equiv.refl _
  map_smul _ _ := rfl
  map_selected := rfl

/-- Reverse a based transport of finite-cover branch actions.-/
def symm (T : FiniteCoverBasedBranchEquiv h h') :
    FiniteCoverBasedBranchEquiv h' h where
  deckEquiv := T.deckEquiv.symm
  branchEquiv := T.branchEquiv.symm
  map_smul σ b := by
    apply T.branchEquiv.injective
    calc
      T.branchEquiv (T.branchEquiv.symm (σ • b)) = σ • b := by simp
      _ = T.deckEquiv (T.deckEquiv.symm σ) •
          T.branchEquiv (T.branchEquiv.symm b) := by simp
      _ = T.branchEquiv
          (T.deckEquiv.symm σ • T.branchEquiv.symm b) :=
        (T.map_smul _ _).symm
  map_selected := by
    apply T.branchEquiv.injective
    simp [T.map_selected]

/-- Compose two based transports of finite-cover branch actions.-/
def trans {E'' L'' : IntermediateField k Ω} {h'' : E'' ≤ L''}
    (T : FiniteCoverBasedBranchEquiv h h')
    (U : FiniteCoverBasedBranchEquiv h' h'') :
    FiniteCoverBasedBranchEquiv h h'' where
  deckEquiv := T.deckEquiv.trans U.deckEquiv
  branchEquiv := T.branchEquiv.trans U.branchEquiv
  map_smul σ b := by
    change U.branchEquiv (T.branchEquiv (σ • b)) =
      U.deckEquiv (T.deckEquiv σ) •
        U.branchEquiv (T.branchEquiv b)
    rw [T.map_smul, U.map_smul]
  map_selected := by
    change U.branchEquiv (T.branchEquiv (finiteCoverSelectedBranch h)) =
      finiteCoverSelectedBranch h''
    rw [T.map_selected, U.map_selected]

/-- Based branch transports are determined by their deck and branch
equivalences; the compatibility witnesses are propositions.
@isnad1 id=eq.4h8v.s11.1f0d5fc77b06 from=translated src=- shape=f2162ae4 vocab=f6ab8b5e
-/
@[ext] theorem ext {T U : FiniteCoverBasedBranchEquiv h h'}
    (hdeck : T.deckEquiv = U.deckEquiv)
    (hbranch : T.branchEquiv = U.branchEquiv) : T = U := by
  cases T
  cases U
  cases hdeck
  cases hbranch
  rfl

end FiniteCoverBasedBranchEquiv

/-- A chosen arrow from the literal branch to any conjugate branch of a
finite normal cover.  Connectedness makes the relevant hom-set nonempty;
the choice is deliberately kept behind this interface.-/
def finiteCoverSelectedArrow [IsAlgClosed Ω]
    (h : E ≤ L) (hfin : FiniteDimensional (↥E) (↥(extendScalars h)))
    (b : finiteCoverBranchGroupoid h) :
    finiteCoverSelectedObject h ⟶ b := by
  let hex := finiteCoverBranch_exists_smul_eq h hfin
    (finiteCoverSelectedBranch h) b.back
  let σ := Classical.choose hex
  have hσ := Classical.choose_spec hex
  exact ⟨σ, hσ⟩

/-- Every conjugate branch of a finite normal cover carries the rational
group chunk obtained from arrows based at the literal selected branch.-/
def finiteCoverArrowChunk [IsAlgClosed Ω]
    (h : E ≤ L) (hfin : FiniteDimensional (↥E) (↥(extendScalars h)))
    (b : finiteCoverBranchGroupoid h) :
    RationalGroupChunk (finiteCoverSelectedObject h ⟶ b) :=
  groupoidArrowChunk (finiteCoverSelectedArrow h hfin b)

end FiniteCoverBranches

end

end AclGeom
