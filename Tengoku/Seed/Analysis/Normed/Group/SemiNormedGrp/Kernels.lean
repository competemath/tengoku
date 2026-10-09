/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Johan Commelin, Kim Morrison
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Normed.Group.SemiNormedGrp
public import Tengoku.Seed.Analysis.Normed.Group.Quotient
public import Tengoku.Seed.CategoryTheory.Limits.Shapes.Kernels

/-!
# Kernels and cokernels in SemiNormedGrp₁ and SemiNormedGrp

We show that `SemiNormedGrp₁` has cokernels
(for which of course the `cokernel.π f` maps are norm non-increasing),
as well as the easier result that `SemiNormedGrp` has cokernels. We also show that
`SemiNormedGrp` has kernels.

So far, I don't see a way to state nicely what we really want:
`SemiNormedGrp` has cokernels, and `cokernel.π f` is norm non-increasing.
The problem is that the limits API doesn't promise you any particular model of the cokernel,
and in `SemiNormedGrp` one can always take a cokernel and rescale its norm
(and hence making `cokernel.π f` arbitrarily large in norm), obtaining another categorical cokernel.

-/

@[expose] public section


open CategoryTheory CategoryTheory.Limits

universe u

namespace SemiNormedGrp₁

noncomputable section

set_option backward.isDefEq.respectTransparency.types false in
/-- Auxiliary definition for `HasCokernels SemiNormedGrp₁`. -/
def cokernelCocone {X Y : SemiNormedGrp₁.{u}} (f : X ⟶ Y) : Cofork f 0 :=
  Cofork.ofπ
    (@SemiNormedGrp₁.mkHom _ (Y ⧸ NormedAddGroupHom.range f.1) _ _
      f.hom.1.range.normedMk (NormedAddGroupHom.isQuotientQuotient _).norm_le)
    (by
      ext x
      rw [Limits.zero_comp, comp_apply, SemiNormedGrp₁.mkHom_apply,
        SemiNormedGrp₁.zero_apply, ← NormedAddGroupHom.mem_ker, f.hom.1.range.ker_normedMk,
        f.hom.1.mem_range]
      use x)

/-- Auxiliary definition for `HasCokernels SemiNormedGrp₁`. -/
def cokernelLift {X Y : SemiNormedGrp₁.{u}} (f : X ⟶ Y) (s : CokernelCofork f) :
    (cokernelCocone f).pt ⟶ s.pt := by
  fconstructor
  -- The lift itself:
  · apply NormedAddGroupHom.lift _ s.π.1
    rintro _ ⟨b, rfl⟩
    change (f ≫ s.π) b = 0
    simp
  -- The lift has norm at most one:
  exact NormedAddGroupHom.lift_normNoninc _ _ _ s.π.2

instance : HasCokernels SemiNormedGrp₁.{u} where
  has_colimit f :=
    HasColimit.mk
      { cocone := cokernelCocone f
        isColimit :=
          isColimitAux _ (cokernelLift f)
            (fun s => by
              ext
              apply NormedAddGroupHom.lift_mk f.1.range
              rintro _ ⟨b, rfl⟩
              change (f ≫ s.π) b = 0
              simp)
            fun _ _ w =>
            SemiNormedGrp₁.hom_ext <| Subtype.ext
              (NormedAddGroupHom.lift_unique f.1.range _ _ _
                (congr_arg Subtype.val (congr_arg Hom.hom w))) }

-- Sanity check
example : HasCokernels SemiNormedGrp₁ := by infer_instance

end

end SemiNormedGrp₁

namespace SemiNormedGrp

section EqualizersAndKernels

noncomputable instance {V W : SemiNormedGrp.{u}} : Norm (V ⟶ W) where
  norm f := norm f.hom
noncomputable instance {V W : SemiNormedGrp.{u}} : NNNorm (V ⟶ W) where
  nnnorm f := nnnorm f.hom

/-- The equalizer cone for a parallel pair of morphisms of seminormed groups. -/
noncomputable def fork {V W : SemiNormedGrp.{u}} (f g : V ⟶ W) : Fork f g :=
  @Fork.ofι _ _ _ _ _ _ (of (f - g).hom.ker)
    (ofHom (NormedAddGroupHom.incl (f - g).hom.ker)) <| by
    ext v
    have : v.1 ∈ (f - g).hom.ker := v.2
    simpa [-SetLike.coe_mem, NormedAddGroupHom.mem_ker, sub_eq_zero] using this

/--
@isnad1 id=haslimit.0h4v.s5.949ce3cf1194 from=seed src=0 shape=a84bb473 vocab=f1c404b4
-/
instance hasLimit_parallelPair {V W : SemiNormedGrp.{u}} (f g : V ⟶ W) :
    HasLimit (parallelPair f g) where
  exists_limit :=
    Nonempty.intro
      { cone := fork f g
        isLimit :=
          have := fun (c : Fork f g) =>
            show NormedAddGroupHom.compHom (f - g).hom c.ι.hom = 0 by
              rw [hom_sub, map_sub, AddMonoidHom.sub_apply, sub_eq_zero]
              exact congr_arg Hom.hom c.condition
          Fork.IsLimit.mk _
            (fun c => ofHom <|
              NormedAddGroupHom.ker.lift (Fork.ι c).hom _ <| this c)
            (fun _ => SemiNormedGrp.hom_ext <| NormedAddGroupHom.ker.incl_comp_lift _ _ (this _))
            fun c g h => by ext x; dsimp; simp_rw [← h]; rfl }

instance : Limits.HasEqualizers.{u, u + 1} SemiNormedGrp :=
  @hasEqualizers_of_hasLimit_parallelPair SemiNormedGrp _ fun {_ _ f g} =>
    SemiNormedGrp.hasLimit_parallelPair f g

end EqualizersAndKernels

section Cokernel

-- PROJECT: can we reuse the work to construct cokernels in `SemiNormedGrp₁` here?
-- I don't see a way to do this that is less work than just repeating the relevant parts.
/-- Auxiliary definition for `HasCokernels SemiNormedGrp`. -/
noncomputable
def cokernelCocone {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) : Cofork f 0 :=
  Cofork.ofπ (P := SemiNormedGrp.of (Y ⧸ NormedAddGroupHom.range f.hom))
    (ofHom f.hom.range.normedMk)
    (by aesop)

/-- Auxiliary definition for `HasCokernels SemiNormedGrp`. -/
noncomputable
def cokernelLift {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) (s : CokernelCofork f) :
    (cokernelCocone f).pt ⟶ s.pt :=
  ofHom <| NormedAddGroupHom.lift _ s.π.hom
    (by
      rintro _ ⟨b, rfl⟩
      change (f ≫ s.π) b = 0
      simp)

/-- Auxiliary definition for `HasCokernels SemiNormedGrp`. -/
noncomputable
def isColimitCokernelCocone {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) :
    IsColimit (cokernelCocone f) :=
  isColimitAux _ (cokernelLift f)
    (fun s => by
      ext
      apply NormedAddGroupHom.lift_mk f.hom.range
      rintro _ ⟨b, rfl⟩
      change (f ≫ s.π) b = 0
      simp)
    fun _ _ w => SemiNormedGrp.hom_ext <| NormedAddGroupHom.lift_unique f.hom.range _ _ _ <|
      congr_arg Hom.hom w

instance : HasCokernels SemiNormedGrp.{u} where
  has_colimit f :=
    HasColimit.mk
      { cocone := cokernelCocone f
        isColimit := isColimitCokernelCocone f }

-- Sanity check
example : HasCokernels SemiNormedGrp := by infer_instance

section ExplicitCokernel

/-- An explicit choice of cokernel, which has good properties with respect to the norm. -/
noncomputable
def explicitCokernel {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) : SemiNormedGrp.{u} :=
  (cokernelCocone f).pt

/-- Descend to the explicit cokernel. -/
noncomputable
def explicitCokernelDesc {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (w : f ≫ g = 0) :
    explicitCokernel f ⟶ Z :=
  (isColimitCokernelCocone f).desc (Cofork.ofπ g (by simp [w]))

/-- The projection from `Y` to the explicit cokernel of `X ⟶ Y`. -/
noncomputable
def explicitCokernelπ {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) : Y ⟶ explicitCokernel f :=
  (cokernelCocone f).ι.app WalkingParallelPair.one

/--
@isnad1 id=surjecti.0h3v.s6.cfe86d5b4aa4 from=seed src=0 shape=b84f7d5e vocab=1abe4bf2
-/
theorem explicitCokernelπ_surjective {X Y : SemiNormedGrp.{u}} {f : X ⟶ Y} :
    Function.Surjective (explicitCokernelπ f) :=
  Quot.mk_surjective

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h3v.s6.29bc957e3c67 from=seed src=0 shape=c4ad16f9 vocab=638b3c26
-/
@[reassoc (attr := simp)]
theorem comp_explicitCokernelπ {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) :
    f ≫ explicitCokernelπ f = 0 := by
  convert! (cokernelCocone f).w WalkingParallelPairHom.left
  simp

/--
@isnad1 id=eq.0h4v.s7.f1d230c75637 from=seed src=0 shape=9755ddc1 vocab=8ae8f297
-/
@[simp]
theorem explicitCokernelπ_apply_dom_eq_zero {X Y : SemiNormedGrp.{u}} {f : X ⟶ Y} (x : X) :
    (explicitCokernelπ f) (f x) = 0 :=
  show (f ≫ explicitCokernelπ f) x = 0 by rw [comp_explicitCokernelπ]; rfl

/--
@isnad1 id=eq.1h5v.s6.9cd38ec9c081 from=seed src=0 shape=93d95ecb vocab=60998416
-/
@[simp, reassoc]
theorem explicitCokernelπ_desc {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (w : f ≫ g = 0) : explicitCokernelπ f ≫ explicitCokernelDesc w = g :=
  (isColimitCokernelCocone f).fac _ _

/--
@isnad1 id=eq.1h6v.s8.300e74ddf661 from=seed src=0 shape=9719e807 vocab=a2a1af97
-/
@[simp]
theorem explicitCokernelπ_desc_apply {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {cond : f ≫ g = 0} (x : Y) : explicitCokernelDesc cond (explicitCokernelπ f x) = g x :=
  show (explicitCokernelπ f ≫ explicitCokernelDesc cond) x = g x by rw [explicitCokernelπ_desc]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
@isnad1 id=eq.2h6v.s7.876a2c2d74cb from=seed src=0 shape=f212344c vocab=60998416
-/
theorem explicitCokernelDesc_unique {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (w : f ≫ g = 0) (e : explicitCokernel f ⟶ Z) (he : explicitCokernelπ f ≫ e = g) :
    e = explicitCokernelDesc w := by
  apply (isColimitCokernelCocone f).uniq (Cofork.ofπ g (by simp [w]))
  rintro (_ | _)
  · convert! w.symm
    simp
  · exact he

/--
@isnad1 id=eq.1h7v.s7.47a92b58a153 from=seed src=0 shape=a5ccff39 vocab=dfcc78b6
-/
theorem explicitCokernelDesc_comp_eq_desc {X Y Z W : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {h : Z ⟶ W} {cond : f ≫ g = 0} :
    explicitCokernelDesc cond ≫ h =
      explicitCokernelDesc
        (show f ≫ g ≫ h = 0 by rw [← CategoryTheory.Category.assoc, cond, Limits.zero_comp]) := by
  refine explicitCokernelDesc_unique _ _ ?_
  rw [← CategoryTheory.Category.assoc, explicitCokernelπ_desc]

/--
@isnad1 id=eq.0h4v.s7.93ab93956f84 from=seed src=0 shape=89583ffa vocab=02ba4460
-/
@[simp]
theorem explicitCokernelDesc_zero {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} :
    explicitCokernelDesc (show f ≫ (0 : Y ⟶ Z) = 0 from CategoryTheory.Limits.comp_zero) = 0 :=
  Eq.symm <| explicitCokernelDesc_unique _ _ CategoryTheory.Limits.comp_zero

/--
@isnad1 id=eq.1h6v.s6.2c6e673bc001 from=seed src=0 shape=c39ed26f vocab=638b3c26
-/
@[ext]
theorem explicitCokernel_hom_ext {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y}
    (e₁ e₂ : explicitCokernel f ⟶ Z) (h : explicitCokernelπ f ≫ e₁ = explicitCokernelπ f ≫ e₂) :
    e₁ = e₂ := by
  let g : Y ⟶ Z := explicitCokernelπ f ≫ e₂
  have w : f ≫ g = 0 := by simp [g]
  have : e₂ = explicitCokernelDesc w := by apply explicitCokernelDesc_unique; rfl
  rw [this]
  apply explicitCokernelDesc_unique
  exact h

/--
@isnad1 id=epi.0h3v.s4.c77922888e12 from=seed src=0 shape=5d0a3199 vocab=334cb314
-/
instance explicitCokernelπ.epi {X Y : SemiNormedGrp.{u}} {f : X ⟶ Y} :
    Epi (explicitCokernelπ f) := by
  constructor
  intro Z g h H
  ext x
  rw [H]

/--
@isnad1 id=isquotie.0h3v.s5.3be3776c6946 from=seed src=0 shape=dcb96b70 vocab=86f53f8b
-/
theorem isQuotient_explicitCokernelπ {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) :
    NormedAddGroupHom.IsQuotient (explicitCokernelπ f).hom :=
  NormedAddGroupHom.isQuotientQuotient _

/--
@isnad1 id=normnoni.0h3v.s5.4778c1ff272c from=seed src=0 shape=dcb96b70 vocab=868ef73d
-/
theorem normNoninc_explicitCokernelπ {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) :
    (explicitCokernelπ f).hom.NormNoninc :=
  (isQuotient_explicitCokernelπ f).norm_le

open scoped NNReal

/--
@isnad1 id=le.2h6v.s6.24906dec31df from=seed src=0 shape=8e445b23 vocab=d2f47704
-/
theorem explicitCokernelDesc_norm_le_of_norm_le {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y}
    {g : Y ⟶ Z} (w : f ≫ g = 0) (c : ℝ≥0) (h : ‖g‖ ≤ c) : ‖explicitCokernelDesc w‖ ≤ c :=
  NormedAddGroupHom.lift_norm_le _ _ _ h

/--
@isnad1 id=normnoni.2h5v.s6.31fe05a9f3e3 from=seed src=0 shape=9df09a2a vocab=18e99ad8
-/
theorem explicitCokernelDesc_normNoninc {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {cond : f ≫ g = 0} (hg : g.hom.NormNoninc) : (explicitCokernelDesc cond).hom.NormNoninc := by
  refine NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.2 ?_
  rw [← NNReal.coe_one]
  exact
    explicitCokernelDesc_norm_le_of_norm_le cond 1
      (NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.1 hg)

/--
@isnad1 id=eq.2h7v.s7.4fad3a20c629 from=seed src=0 shape=2ba3588b vocab=15cf8af1
-/
theorem explicitCokernelDesc_comp_eq_zero {X Y Z W : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {h : Z ⟶ W} (cond : f ≫ g = 0) (cond2 : g ≫ h = 0) : explicitCokernelDesc cond ≫ h = 0 := by
  rw [← cancel_epi (explicitCokernelπ f), ← Category.assoc, explicitCokernelπ_desc]
  simp [cond2]

/--
@isnad1 id=le.1h5v.s6.3672429e1397 from=seed src=0 shape=693a1cae vocab=0061188a
-/
theorem explicitCokernelDesc_norm_le {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (w : f ≫ g = 0) : ‖explicitCokernelDesc w‖ ≤ ‖g‖ :=
  explicitCokernelDesc_norm_le_of_norm_le w ‖g‖₊ le_rfl

/-- The explicit cokernel is isomorphic to the usual cokernel. -/
noncomputable
def explicitCokernelIso {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) :
    explicitCokernel f ≅ cokernel f :=
  (isColimitCokernelCocone f).coconePointUniqueUpToIso (colimit.isColimit _)

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h3v.s6.555b282242f0 from=seed src=0 shape=e903d38d vocab=ca8ae835
-/
@[simp]
theorem explicitCokernelIso_hom_π {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) :
    explicitCokernelπ f ≫ (explicitCokernelIso f).hom = cokernel.π _ := by
  simp [explicitCokernelπ, explicitCokernelIso, IsColimit.coconePointUniqueUpToIso]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h3v.s6.9a2ed5245717 from=seed src=0 shape=1eecc66b vocab=e0f2191b
-/
@[simp]
theorem explicitCokernelIso_inv_π {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) :
    cokernel.π f ≫ (explicitCokernelIso f).inv = explicitCokernelπ f := by
  simp [explicitCokernelπ, explicitCokernelIso]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.1h5v.s7.f14ff9421a46 from=seed src=0 shape=9b17673f vocab=8b8a2bb3
-/
@[simp]
theorem explicitCokernelIso_hom_desc {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (w : f ≫ g = 0) :
    (explicitCokernelIso f).hom ≫ cokernel.desc f g w = explicitCokernelDesc w := by
  ext1
  simp [explicitCokernelDesc, explicitCokernelπ, explicitCokernelIso,
    IsColimit.coconePointUniqueUpToIso]

/-- A special case of `CategoryTheory.Limits.cokernel.map` adapted to `explicitCokernel`. -/
noncomputable def explicitCokernel.map {A B C D : SemiNormedGrp.{u}}
    {fab : A ⟶ B} {fbd : B ⟶ D} {fac : A ⟶ C} {fcd : C ⟶ D} (h : fab ≫ fbd = fac ≫ fcd) :
    explicitCokernel fab ⟶ explicitCokernel fcd :=
  @explicitCokernelDesc _ _ _ fab (fbd ≫ explicitCokernelπ _) <| by simp [reassoc_of% h]

/-- A special case of `CategoryTheory.Limits.cokernel.map_desc` adapted to `explicitCokernel`.
@isnad1 id=eq.4h13v.s8.f6bd3050b466 from=seed src=0 shape=5782f7df vocab=a8f7726f
-/
theorem ExplicitCoker.map_desc {A B C D B' D' : SemiNormedGrp.{u}}
    {fab : A ⟶ B} {fbd : B ⟶ D} {fac : A ⟶ C} {fcd : C ⟶ D} {h : fab ≫ fbd = fac ≫ fcd}
    {fbb' : B ⟶ B'} {fdd' : D ⟶ D'} {condb : fab ≫ fbb' = 0} {condd : fcd ≫ fdd' = 0} {g : B' ⟶ D'}
    (h' : fbb' ≫ g = fbd ≫ fdd') :
    explicitCokernelDesc condb ≫ g = explicitCokernel.map h ≫ explicitCokernelDesc condd := by
  delta explicitCokernel.map
  simp only [← Category.assoc, ← cancel_epi (explicitCokernelπ fab)]
  simp [Category.assoc, explicitCokernelπ_desc, h']

end ExplicitCokernel

end Cokernel

end SemiNormedGrp
