/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicGeometry.SpreadingOut
public import Tengoku.Seed.AlgebraicGeometry.FunctionField
public import Tengoku.Seed.AlgebraicGeometry.Morphisms.Separated
/-!

# Rational maps between schemes

## Main definitions

* `AlgebraicGeometry.Scheme.PartialMap`: A partial map from `X` to `Y` (`X.PartialMap Y`) is
  a morphism into `Y` defined on a dense open subscheme of `X`.
* `AlgebraicGeometry.Scheme.PartialMap.equiv`:
  Two partial maps are equivalent if they are equal on a dense open subscheme.
* `AlgebraicGeometry.Scheme.RationalMap`:
  A rational map from `X` to `Y` (`X ⤏ Y`) is an equivalence class of partial maps.
* `AlgebraicGeometry.Scheme.RationalMap.equivFunctionFieldOver`:
  Given `S`-schemes `X` and `Y` such that `Y` is locally of finite type and `X` is integral,
  `S`-morphisms `Spec K(X) ⟶ Y` correspond bijectively to `S`-rational maps from `X` to `Y`.
* `AlgebraicGeometry.Scheme.RationalMap.toPartialMap`:
  If `X` is reduced and `Y` is separated, then any `f : X ⤏ Y` can be realized as a partial
  map on `f.domain`, the domain of definition of `f`.
-/

@[expose] public section

universe u

open CategoryTheory hiding Quotient

namespace AlgebraicGeometry

variable {X Y Z S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)

namespace Scheme

/--
A partial map from `X` to `Y` (`X.PartialMap Y`) is a morphism into `Y`
defined on a dense open subscheme of `X`.
-/
structure PartialMap (X Y : Scheme.{u}) where
  /-- The domain of definition of a partial map. -/
  domain : X.Opens
  dense_domain : Dense (domain : Set X)
  /-- The underlying morphism of a partial map. -/
  hom : ↑domain ⟶ Y

variable (S) in
/-- A partial map is an `S`-map if the underlying morphism is. -/
abbrev PartialMap.IsOver [X.Over S] [Y.Over S] (f : X.PartialMap Y) :=
  f.hom.IsOver S

namespace PartialMap

/--
@isnad1 id=iff.0h4v.s6.7059b325817c from=seed src=0 shape=2d7cae91 vocab=18694d11
-/
lemma ext_iff (f g : X.PartialMap Y) :
    f = g ↔ ∃ e : f.domain = g.domain, f.hom = (X.isoOfEq e).hom ≫ g.hom := by
  constructor
  · rintro rfl
    simp
  · obtain ⟨U, hU, f⟩ := f
    obtain ⟨V, hV, g⟩ := g
    rintro ⟨rfl : U = V, e⟩
    congr 1
    simpa using e

/--
@isnad1 id=eq.2h4v.s6.f24c06f2e34a from=seed src=0 shape=8e0a65e6 vocab=18694d11
-/
@[ext]
lemma ext (f g : X.PartialMap Y) (e : f.domain = g.domain)
    (H : f.hom = (X.isoOfEq e).hom ≫ g.hom) : f = g := by
  rw [ext_iff]
  exact ⟨e, H⟩

/-- The restriction of a partial map to a smaller domain. -/
@[simps hom domain]
noncomputable
def restrict (f : X.PartialMap Y) (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) : X.PartialMap Y where
  domain := U
  dense_domain := hU
  hom := X.homOfLE hU' ≫ f.hom

set_option backward.defeqAttrib.useBackward true in
/--
@isnad1 id=eq.0h3v.s4.e98325bf6f15 from=seed src=0 shape=07596069 vocab=269c97e9
-/
@[simp]
lemma restrict_id (f : X.PartialMap Y) : f.restrict f.domain f.dense_domain le_rfl = f := by
  ext1 <;> simp [restrict_domain]

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h3v.s5.0b85a0cc501d from=seed src=0 shape=d349ffb3 vocab=df67edf3
-/
lemma restrict_id_hom (f : X.PartialMap Y) :
    (f.restrict f.domain f.dense_domain le_rfl).hom = f.hom := by
  simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
@isnad1 id=eq.4h5v.s7.a605643e75d4 from=seed src=0 shape=f07114e8 vocab=369269c0
-/
@[simp]
lemma restrict_restrict (f : X.PartialMap Y)
    (U : X.Opens) (hU : Dense (U : Set X)) (hU' : U ≤ f.domain)
    (V : X.Opens) (hV : Dense (V : Set X)) (hV' : V ≤ U) :
    (f.restrict U hU hU').restrict V hV hV' = f.restrict V hV (hV'.trans hU') := by
  ext1 <;> simp [restrict_domain]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
@isnad1 id=eq.4h5v.s7.8f62ba68f771 from=seed src=0 shape=e3737bb2 vocab=2229a17d
-/
lemma restrict_restrict_hom (f : X.PartialMap Y)
    (U : X.Opens) (hU : Dense (U : Set X)) (hU' : U ≤ f.domain)
    (V : X.Opens) (hV : Dense (V : Set X)) (hV' : V ≤ U) :
    ((f.restrict U hU hU').restrict V hV hV').hom = (f.restrict V hV (hV'.trans hU')).hom := by
  simp

set_option backward.defeqAttrib.useBackward true in
instance [X.Over S] [Y.Over S] (f : X.PartialMap Y) [f.IsOver S]
    (U : X.Opens) (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) :
    (f.restrict U hU hU').IsOver S where

/-- The composition of a partial map and a morphism on the right. -/
@[simps]
def compHom (f : X.PartialMap Y) (g : Y ⟶ Z) : X.PartialMap Z where
  domain := f.domain
  dense_domain := f.dense_domain
  hom := f.hom ≫ g

set_option backward.defeqAttrib.useBackward true in
/--
@isnad1 id=eq.0h3v.s4.a0d9f7d6a4fb from=seed src=0 shape=6fa9f053 vocab=ea6ff024
-/
@[simp]
lemma compHom_id (f : X.PartialMap Y) : f.compHom (𝟙 Y) = f := by
  ext <;> simp

set_option backward.defeqAttrib.useBackward true in
instance [X.Over S] [Y.Over S] [Z.Over S] (f : X.PartialMap Y) (g : Y ⟶ Z)
    [f.IsOver S] [g.IsOver S] : (f.compHom g).IsOver S where

/-- A scheme morphism as a partial map. -/
@[simps]
def _root_.AlgebraicGeometry.Scheme.Hom.toPartialMap (f : X ⟶ Y) :
    X.PartialMap Y := ⟨⊤, dense_univ, X.topIso.hom ≫ f⟩

set_option backward.defeqAttrib.useBackward true in
instance (f : X ⟶ Y) [IsDominant f] : IsDominant f.toPartialMap.hom := by
  dsimp
  have := Opens.isDominant_ι (X := X) (U := ⊤) dense_univ
  infer_instance

lemma _root_.AlgebraicGeometry.Scheme.Hom.toPartialMap_compHom (f : X ⟶ Y) (g : Y ⟶ Z) :
    f.toPartialMap.compHom g = (f ≫ g).toPartialMap := rfl

variable (X) in
/-- The identity partial map. -/
protected abbrev id : X.PartialMap X := (𝟙 X : X ⟶ X).toPartialMap

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h3v.s4.53b7f8a03c45 from=seed src=0 shape=9ee0cce7 vocab=26cd5b50
-/
@[simp]
lemma id_compHom (f : X ⟶ Y) : (PartialMap.id X).compHom f = f.toPartialMap := by
  apply PartialMap.ext _ _ rfl
  simp

set_option backward.defeqAttrib.useBackward true in
instance [X.Over S] [Y.Over S] (f : X ⟶ Y) [f.IsOver S] : f.toPartialMap.IsOver S where

set_option backward.defeqAttrib.useBackward true in
/--
@isnad1 id=iff.0h4v.s6.9ebce0a0954f from=seed src=0 shape=d07cf043 vocab=7affd81f
-/
lemma isOver_iff [X.Over S] [Y.Over S] {f : X.PartialMap Y} :
    f.IsOver S ↔ (f.compHom (Y ↘ S)).hom = f.domain.ι ≫ X ↘ S := by
  simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
@isnad1 id=iff.0h4v.s6.7821d295c5d5 from=seed src=0 shape=5a021e88 vocab=a8ac019c
-/
lemma isOver_iff_eq_restrict [X.Over S] [Y.Over S] {f : X.PartialMap Y} :
    f.IsOver S ↔ f.compHom (Y ↘ S) = (X ↘ S).toPartialMap.restrict _ f.dense_domain (by simp) := by
  simp [PartialMap.ext_iff]

/-- If `x` is in the domain of a partial map `f`, then `f` restricts to a map from `Spec 𝒪_x`. -/
noncomputable
def fromSpecStalkOfMem (f : X.PartialMap Y) {x} (hx : x ∈ f.domain) :
    Spec (X.presheaf.stalk x) ⟶ Y :=
  f.domain.fromSpecStalkOfMem x hx ≫ f.hom

/-- A partial map restricts to a map from `Spec K(X)`. -/
noncomputable
abbrev fromFunctionField [IrreducibleSpace X] (f : X.PartialMap Y) :
    Spec X.functionField ⟶ Y :=
  f.fromSpecStalkOfMem
    ((genericPoint_specializes _).mem_open f.domain.2 f.dense_domain.nonempty.choose_spec)

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.3h5v.s7.3ff754390c2d from=seed src=0 shape=d7b1edcb vocab=a06136c7
-/
lemma fromSpecStalkOfMem_restrict (f : X.PartialMap Y)
    {U : X.Opens} (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) {x} (hx : x ∈ U) :
    (f.restrict U hU hU').fromSpecStalkOfMem hx = f.fromSpecStalkOfMem (hU' hx) := by
  dsimp only [fromSpecStalkOfMem, restrict, Scheme.Opens.fromSpecStalkOfMem]
  have e : ⟨x, hU' hx⟩ = X.homOfLE hU' ⟨x, hx⟩ := by
    rw [Scheme.homOfLE_base]
    rfl
  rw [Category.assoc, ← SpecMap_stalkMap_fromSpecStalk_assoc,
    ← SpecMap_stalkSpecializes_fromSpecStalk (Inseparable.of_eq e).specializes,
    ← TopCat.Presheaf.stalkCongr_inv _ (Inseparable.of_eq e)]
  simp only [← Category.assoc, ← Spec.map_comp]
  congr 3
  rw [Iso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq, IsIso.eq_inv_comp,
    Hom.stalkMap_congr_hom _ _ (X.homOfLE_ι hU').symm]
  simp only [TopCat.Presheaf.stalkCongr_hom]
  rw [← Hom.stalkSpecializes_stalkMap_assoc, Hom.stalkMap_comp]

/--
@isnad1 id=eq.2h4v.s7.4fe380263cf3 from=seed src=0 shape=4457b0fa vocab=557fff76
-/
lemma fromFunctionField_restrict (f : X.PartialMap Y) [IrreducibleSpace X]
    {U : X.Opens} (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) :
    (f.restrict U hU hU').fromFunctionField = f.fromFunctionField :=
  fromSpecStalkOfMem_restrict f _ _ _

/--
Given `S`-schemes `X` and `Y` such that `Y` is locally of finite type and
`X` is irreducible germ-injective at `x` (e.g. when `X` is integral),
any `S`-morphism `Spec 𝒪ₓ ⟶ Y` spreads out to a partial map from `X` to `Y`.
-/
noncomputable
def ofFromSpecStalk [IrreducibleSpace X] [LocallyOfFiniteType sY] {x : X} [X.IsGermInjectiveAt x]
    (φ : Spec (X.presheaf.stalk x) ⟶ Y) (h : φ ≫ sY = X.fromSpecStalk x ≫ sX) : X.PartialMap Y where
  hom := (spread_out_of_isGermInjective' sX sY φ h).choose_spec.choose_spec.choose
  domain := (spread_out_of_isGermInjective' sX sY φ h).choose
  dense_domain := (spread_out_of_isGermInjective' sX sY φ h).choose.2.dense
    ⟨_, (spread_out_of_isGermInjective' sX sY φ h).choose_spec.choose⟩

/--
@isnad1 id=eq.1h7v.s8.a51840e62125 from=seed src=0 shape=be2d8ff0 vocab=73efae1e
-/
lemma ofFromSpecStalk_comp [IrreducibleSpace X] [LocallyOfFiniteType sY]
    {x : X} [X.IsGermInjectiveAt x] (φ : Spec (X.presheaf.stalk x) ⟶ Y)
    (h : φ ≫ sY = X.fromSpecStalk x ≫ sX) :
    (ofFromSpecStalk sX sY φ h).hom ≫ sY = (ofFromSpecStalk sX sY φ h).domain.ι ≫ sX :=
  (spread_out_of_isGermInjective' sX sY φ h).choose_spec.choose_spec.choose_spec.2

/--
@isnad1 id=mem.1h7v.s8.34be9ab165b9 from=seed src=0 shape=a2a2ab75 vocab=7b3d7333
-/
lemma mem_domain_ofFromSpecStalk [IrreducibleSpace X] [LocallyOfFiniteType sY]
    {x : X} [X.IsGermInjectiveAt x] (φ : Spec (X.presheaf.stalk x) ⟶ Y)
    (h : φ ≫ sY = X.fromSpecStalk x ≫ sX) : x ∈ (ofFromSpecStalk sX sY φ h).domain :=
  (spread_out_of_isGermInjective' sX sY φ h).choose_spec.choose

/--
@isnad1 id=eq.1h7v.s7.0ae0727687de from=seed src=0 shape=e5bc6d4d vocab=b823e955
-/
lemma fromSpecStalkOfMem_ofFromSpecStalk [IrreducibleSpace X] [LocallyOfFiniteType sY]
    {x : X} [X.IsGermInjectiveAt x] (φ : Spec (X.presheaf.stalk x) ⟶ Y)
    (h : φ ≫ sY = X.fromSpecStalk x ≫ sX) :
    (ofFromSpecStalk sX sY φ h).fromSpecStalkOfMem (mem_domain_ofFromSpecStalk sX sY φ h) = φ :=
  (spread_out_of_isGermInjective' sX sY φ h).choose_spec.choose_spec.choose_spec.1.symm

set_option backward.defeqAttrib.useBackward true in
/--
@isnad1 id=eq.1h6v.s7.8bf80ddaa64a from=seed src=0 shape=0c169a7f vocab=767a27a7
-/
@[simp]
lemma fromSpecStalkOfMem_compHom (f : X.PartialMap Y) (g : Y ⟶ Z) (x) (hx) :
    (f.compHom g).fromSpecStalkOfMem (x := x) hx = f.fromSpecStalkOfMem hx ≫ g := by
  simp [fromSpecStalkOfMem]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
@isnad1 id=eq.0h4v.s6.cdeea7004c3b from=seed src=0 shape=e2f5fc99 vocab=302d9f6f
-/
@[simp]
lemma fromSpecStalkOfMem_toPartialMap (f : X ⟶ Y) (x) :
    f.toPartialMap.fromSpecStalkOfMem (x := x) trivial = X.fromSpecStalk x ≫ f := by
  simp [fromSpecStalkOfMem]

/-- Two partial maps are equivalent if they are equal on a dense open subscheme. -/
protected noncomputable
def equiv (f g : X.PartialMap Y) : Prop :=
  ∃ (W : X.Opens) (hW : Dense (W : Set X)) (hWl : W ≤ f.domain) (hWr : W ≤ g.domain),
    (f.restrict W hW hWl).hom = (g.restrict W hW hWr).hom

/--
@isnad1 id=equiv.5h6v.s7.fcfbafe47d21 from=seed src=0 shape=94dd5574 vocab=d97ef1cd
-/
lemma equiv_of_restrict_eq (f g : X.PartialMap Y) {W₁ W₂ : X.Opens} {hW₁ : Dense (W₁ : Set X)}
    {hW₂ : Dense (W₂ : Set X)} {hW₁' : W₁ ≤ f.domain} {hW₂' : W₂ ≤ g.domain}
    (H : f.restrict W₁ hW₁ hW₁' = g.restrict W₂ hW₂ hW₂') : f.equiv g := by
  have e : W₁ = W₂ := congr($(H).domain)
  subst e
  exact ⟨W₁, hW₁, hW₁', hW₂', congr($(H).hom)⟩

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=equiv.0h3v.s3.cad243f54491 from=seed src=0 shape=e523d0cb vocab=ccb7a662
-/
@[refl]
lemma equiv.refl (f : X.PartialMap Y) : f.equiv f :=
  ⟨f.domain, f.dense_domain, by simp⟩

/--
@isnad1 id=equiv.1h4v.s4.524f5c45feec from=seed src=0 shape=6621116b vocab=ccb7a662
-/
@[symm]
lemma equiv.symm {f g : X.PartialMap Y} : f.equiv g → g.equiv f := by
  intro ⟨W, hW, hWl, hWr, e⟩
  exact ⟨W, hW, hWr, hWl, e.symm⟩

set_option backward.defeqAttrib.useBackward true in
/--
@isnad1 id=equiv.2h5v.s5.7744be82b7b4 from=seed src=0 shape=28346d77 vocab=ccb7a662
-/
@[trans]
lemma equiv.trans {f g h : X.PartialMap Y} : f.equiv g → g.equiv h → f.equiv h := by
  intro ⟨W₁, hW₁, hW₁l, hW₁r, e₁⟩ ⟨W₂, hW₂, hW₂l, hW₂r, e₂⟩
  refine ⟨W₁ ⊓ W₂, hW₁.inter_of_isOpen_left hW₂ W₁.2, inf_le_left.trans hW₁l,
    inf_le_right.trans hW₂r, ?_⟩
  dsimp at e₁ e₂
  simp only [restrict_domain, restrict_hom, ← X.homOfLE_homOfLE (U := W₁ ⊓ W₂) inf_le_left hW₁l,
    Category.assoc, e₁, ← X.homOfLE_homOfLE (U := W₁ ⊓ W₂) inf_le_right hW₂r, ← e₂]
  simp only [homOfLE_homOfLE_assoc]

/--
@isnad1 id=equivale.0h2v.s3.cad76848f123 from=seed src=0 shape=f4bb34bc vocab=16022fe3
-/
lemma equivalence_rel : Equivalence (@Scheme.PartialMap.equiv X Y) where
  refl := equiv.refl
  symm := equiv.symm
  trans := equiv.trans

instance : Setoid (X.PartialMap Y) := ⟨@PartialMap.equiv X Y, equivalence_rel⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
@isnad1 id=equiv.2h4v.s6.9303d92cc177 from=seed src=0 shape=aee19f51 vocab=d97ef1cd
-/
lemma restrict_equiv (f : X.PartialMap Y) (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) : (f.restrict U hU hU').equiv f :=
  ⟨U, hU, le_rfl, hU', by simp⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=equiv.3h5v.s7.90f58b8a6573 from=seed src=0 shape=16e774a3 vocab=f7b59a42
-/
lemma equiv_of_fromSpecStalkOfMem_eq [IrreducibleSpace X]
    {x : X} [X.IsGermInjectiveAt x] (f g : X.PartialMap Y)
    (hxf : x ∈ f.domain) (hxg : x ∈ g.domain)
    (H : f.fromSpecStalkOfMem hxf = g.fromSpecStalkOfMem hxg) : f.equiv g := by
  have hdense : Dense ((f.domain ⊓ g.domain) : Set X) :=
    f.dense_domain.inter_of_isOpen_left g.dense_domain f.domain.2
  have := (isGermInjectiveAt_iff_of_isOpenImmersion (f := (f.domain ⊓ g.domain).ι)
    (x := ⟨x, hxf, hxg⟩)).mp ‹_›
  have := spread_out_unique_of_isGermInjective' (X := (f.domain ⊓ g.domain).toScheme)
    (X.homOfLE inf_le_left ≫ f.hom) (X.homOfLE inf_le_right ≫ g.hom) (x := ⟨x, hxf, hxg⟩) ?_
  · obtain ⟨U, hxU, e⟩ := this
    refine ⟨(f.domain ⊓ g.domain).ι ''ᵁ U, ((f.domain ⊓ g.domain).ι ''ᵁ U).2.dense
      ⟨_, ⟨_, hxU, rfl⟩⟩,
      ((Set.image_subset_range _ _).trans_eq (Subtype.range_val)).trans inf_le_left,
      ((Set.image_subset_range _ _).trans_eq (Subtype.range_val)).trans inf_le_right, ?_⟩
    rw [← cancel_epi (Scheme.Hom.isoImage _ _).hom]
    simp only [restrict_hom, ← Category.assoc] at e ⊢
    convert! e using 2 <;> rw [← cancel_mono (Scheme.Opens.ι _)] <;> simp
  · rw [← f.fromSpecStalkOfMem_restrict hdense inf_le_left ⟨hxf, hxg⟩,
      ← g.fromSpecStalkOfMem_restrict hdense inf_le_right ⟨hxf, hxg⟩] at H
    simpa only [fromSpecStalkOfMem, restrict_domain, Opens.fromSpecStalkOfMem, Spec.map_inv,
      restrict_hom, Category.assoc, IsIso.eq_inv_comp, IsIso.hom_inv_id_assoc] using H

set_option backward.isDefEq.respectTransparency false in
/-- Two partial maps from reduced schemes to separated schemes are equivalent if and only if
they are equal on **any** open dense subset.
@isnad1 id=iff.3h6v.s7.24a311d4016b from=seed src=0 shape=65ed8021 vocab=ad71a46a
-/
lemma equiv_iff_of_isSeparated_of_le [X.Over S] [Y.Over S] [IsReduced X]
    [IsSeparated (Y ↘ S)] {f g : X.PartialMap Y} [f.IsOver S] [g.IsOver S]
    {W : X.Opens} (hW : Dense (X := X) W) (hWl : W ≤ f.domain) (hWr : W ≤ g.domain) : f.equiv g ↔
      (f.restrict W hW hWl).hom = (g.restrict W hW hWr).hom := by
  refine ⟨fun ⟨V, hV, hVl, hVr, e⟩ ↦ ?_, fun e ↦ ⟨_, _, _, _, e⟩⟩
  have : IsDominant (X.homOfLE (inf_le_left : W ⊓ V ≤ W)) :=
    Opens.isDominant_homOfLE (hW.inter_of_isOpen_left hV W.2) _
  apply ext_of_isDominant_of_isSeparated' S (X.homOfLE (inf_le_left : W ⊓ V ≤ W))
  simpa using congr(X.homOfLE (inf_le_right : W ⊓ V ≤ V) ≫ $e)

/-- Two partial maps from reduced schemes to separated schemes are equivalent if and only if
they are equal on the intersection of the domains.
@isnad1 id=iff.0h5v.s7.0726c53101d4 from=seed src=0 shape=a8e07b0e vocab=f6a16305
-/
lemma equiv_iff_of_isSeparated [X.Over S] [Y.Over S] [IsReduced X]
    [IsSeparated (Y ↘ S)] {f g : X.PartialMap Y}
    [f.IsOver S] [g.IsOver S] : f.equiv g ↔
      (f.restrict _ (f.2.inter_of_isOpen_left g.2 f.domain.2) inf_le_left).hom =
      (g.restrict _ (f.2.inter_of_isOpen_left g.2 f.domain.2) inf_le_right).hom :=
  equiv_iff_of_isSeparated_of_le (S := S) _ _ _

set_option backward.defeqAttrib.useBackward true in
/-- Two partial maps from reduced schemes to separated schemes with the same domain are equivalent
if and only if they are equal.
@isnad1 id=iff.1h5v.s6.aeb1cb7252e5 from=seed src=0 shape=ee1d559e vocab=dd74599f
-/
lemma equiv_iff_of_domain_eq_of_isSeparated [X.Over S] [Y.Over S] [IsReduced X]
    [IsSeparated (Y ↘ S)] {f g : X.PartialMap Y} (hfg : f.domain = g.domain)
    [f.IsOver S] [g.IsOver S] : f.equiv g ↔ f = g := by
  rw [equiv_iff_of_isSeparated_of_le (S := S) f.dense_domain le_rfl hfg.le]
  obtain ⟨Uf, _, f⟩ := f
  obtain ⟨Ug, _, g⟩ := g
  obtain rfl : Uf = Ug := hfg
  simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A partial map from a reduced scheme to a separated scheme is equivalent to a morphism
if and only if it is equal to the restriction of the morphism.
@isnad1 id=iff.0h5v.s6.362d01c1aeeb from=seed src=0 shape=bc4830cc vocab=3c2aba61
-/
lemma equiv_toPartialMap_iff_of_isSeparated [X.Over S] [Y.Over S] [IsReduced X]
    [IsSeparated (Y ↘ S)] {f : X.PartialMap Y} {g : X ⟶ Y}
    [f.IsOver S] [g.IsOver S] : f.equiv g.toPartialMap ↔
      f.hom = f.domain.ι ≫ g := by
  rw [equiv_iff_of_isSeparated (S := S), ← cancel_epi (X.isoOfEq (inf_top_eq f.domain)).hom]
  simp
  rfl

end PartialMap

/-- A rational map from `X` to `Y` (`X ⤏ Y`) is an equivalence class of partial maps,
where two partial maps are equivalent if they are equal on a dense open subscheme. -/
def RationalMap (X Y : Scheme.{u}) : Type u :=
  @Quotient (X.PartialMap Y) inferInstance

/-- The notation for rational maps. -/
scoped[AlgebraicGeometry] infix:10 " ⤏ " => Scheme.RationalMap

/-- A partial map as a rational map. -/
def PartialMap.toRationalMap (f : X.PartialMap Y) : X ⤏ Y := Quotient.mk _ f

/-- A scheme morphism as a rational map. -/
abbrev Hom.toRationalMap (f : X.Hom Y) : X ⤏ Y := f.toPartialMap.toRationalMap

variable (X) in
/-- The identity rational map. -/
abbrev RationalMap.id : X ⤏ X := (PartialMap.id X).toRationalMap

variable (S) in
/-- A rational map is an `S`-map if some partial map in the equivalence class is an `S`-map. -/
class RationalMap.IsOver [X.Over S] [Y.Over S] (f : X ⤏ Y) : Prop where
  exists_partialMap_over : ∃ g : X.PartialMap Y, g.IsOver S ∧ g.toRationalMap = f

/--
@isnad1 id=surjecti.0h2v.s3.d12f4732fd2d from=seed src=0 shape=e7a9f254 vocab=6c21ee6b
-/
lemma PartialMap.toRationalMap_surjective : Function.Surjective (@toRationalMap X Y) :=
  Quotient.exists_rep

/--
@isnad1 id=ex.0h3v.s4.c255bf69adac from=seed src=0 shape=2fa53ff8 vocab=a0d2bfc0
-/
lemma RationalMap.exists_rep (f : X ⤏ Y) : ∃ g : X.PartialMap Y, g.toRationalMap = f :=
  Quotient.exists_rep f

/--
@isnad1 id=iff.0h4v.s4.6a40251339be from=seed src=0 shape=af0ddb6e vocab=f55889e9
-/
lemma PartialMap.toRationalMap_eq_iff {f g : X.PartialMap Y} :
    f.toRationalMap = g.toRationalMap ↔ f.equiv g :=
  Quotient.eq

/-- An arbitrarily chosen partial map representing `f`. Use `RationalMap.toPartialMap` instead
if `X` is reduced and `Y` is separated. -/
noncomputable def RationalMap.representative (f : X ⤏ Y) : X.PartialMap Y :=
  f.exists_rep.choose

/--
@isnad1 id=eq.0h3v.s4.1ea60cb1f4f2 from=seed src=0 shape=db68ba20 vocab=af9f8d14
-/
@[simp]
lemma RationalMap.toRationalMap_representative (f : X ⤏ Y) :
    f.representative.toRationalMap = f :=
  f.exists_rep.choose_spec

/--
@isnad1 id=equiv.0h3v.s4.d185004fa51b from=seed src=0 shape=e8c97288 vocab=750a2f08
-/
lemma PartialMap.representative_toRationalMap_equiv (f : X.PartialMap Y) :
    f.toRationalMap.representative.equiv f := by
  rw [← PartialMap.toRationalMap_eq_iff, f.toRationalMap.toRationalMap_representative]

/--
@isnad1 id=eq.2h4v.s6.3f0468981598 from=seed src=0 shape=f9a3f384 vocab=202f9c91
-/
@[simp]
lemma PartialMap.restrict_toRationalMap (f : X.PartialMap Y) (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) :
    (f.restrict U hU hU').toRationalMap = f.toRationalMap :=
  toRationalMap_eq_iff.mpr (f.restrict_equiv U hU hU')

instance [X.Over S] [Y.Over S] (f : X.PartialMap Y) [f.IsOver S] : f.toRationalMap.IsOver S :=
  ⟨f, ‹_›, rfl⟩

variable (S) in
/--
@isnad1 id=ex.0h4v.s5.973901ed27f8 from=seed src=0 shape=188d75da vocab=96eb4bf5
-/
lemma RationalMap.exists_partialMap_over [X.Over S] [Y.Over S] (f : X ⤏ Y) [f.IsOver S] :
    ∃ g : X.PartialMap Y, g.IsOver S ∧ g.toRationalMap = f :=
  IsOver.exists_partialMap_over

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The composition of a rational map and a morphism on the right. -/
def RationalMap.compHom (f : X ⤏ Y) (g : Y ⟶ Z) : X ⤏ Z := by
  refine Quotient.map (PartialMap.compHom · g) ?_ f
  intro f₁ f₂ ⟨W, hW, hWl, hWr, e⟩
  refine ⟨W, hW, hWl, hWr, ?_⟩
  simp only [PartialMap.restrict_domain, PartialMap.restrict_hom, PartialMap.compHom_domain,
    PartialMap.compHom_hom] at e ⊢
  rw [reassoc_of% e]

/--
@isnad1 id=eq.0h5v.s5.e3be1d2f80e7 from=seed src=0 shape=400674d9 vocab=33342761
-/
@[simp]
lemma RationalMap.compHom_toRationalMap (f : X.PartialMap Y) (g : Y ⟶ Z) :
    (f.compHom g).toRationalMap = f.toRationalMap.compHom g := rfl

/--
@isnad1 id=eq.0h3v.s4.43c6b91f5484 from=seed src=0 shape=9ee0cce7 vocab=eca06441
-/
@[simp]
lemma RationalMap.id_compHom (f : X ⟶ Y) :
    (RationalMap.id X).compHom f = f.toRationalMap := by
  rw [RationalMap.id, ← compHom_toRationalMap, PartialMap.id_compHom]

instance [X.Over S] [Y.Over S] [Z.Over S] (f : X ⤏ Y) (g : Y ⟶ Z)
    [f.IsOver S] [g.IsOver S] : (f.compHom g).IsOver S where
  exists_partialMap_over := by
    obtain ⟨f, hf, rfl⟩ := f.exists_partialMap_over S
    exact ⟨f.compHom g, inferInstance, rfl⟩

set_option backward.isDefEq.respectTransparency false in
variable (S) in
/--
@isnad1 id=ex.0h4v.s7.fd494412de7a from=seed src=0 shape=734b640b vocab=3c0beaed
-/
lemma PartialMap.exists_restrict_isOver [X.Over S] [Y.Over S] (f : X.PartialMap Y)
    [f.toRationalMap.IsOver S] : ∃ U hU hU', (f.restrict U hU hU').IsOver S := by
  obtain ⟨f', hf₁, hf₂⟩ := RationalMap.IsOver.exists_partialMap_over (S := S) (f := f.toRationalMap)
  obtain ⟨U, hU, hUl, hUr, e⟩ := PartialMap.toRationalMap_eq_iff.mp hf₂
  exact ⟨U, hU, hUr, by rw [IsOver, ← e]; infer_instance⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
@isnad1 id=iff.0h4v.s5.efcb5d6754dd from=seed src=0 shape=fb51ef8a vocab=14d1f16f
-/
lemma RationalMap.isOver_iff [X.Over S] [Y.Over S] {f : X ⤏ Y} :
    f.IsOver S ↔ f.compHom (Y ↘ S) = (X ↘ S).toRationalMap := by
  constructor
  · intro h
    obtain ⟨g, hg, e⟩ := f.exists_partialMap_over S
    rw [← e, Hom.toRationalMap, ← compHom_toRationalMap, PartialMap.isOver_iff_eq_restrict.mp hg,
      PartialMap.restrict_toRationalMap]
  · intro e
    obtain ⟨f, rfl⟩ := PartialMap.toRationalMap_surjective f
    obtain ⟨U, hU, hUl, hUr, e⟩ := PartialMap.toRationalMap_eq_iff.mp e
    exact ⟨⟨f.restrict U hU hUl, by simpa using! e, by simp⟩⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=iff.0h4v.s5.5b90b4f880bf from=seed src=0 shape=4f83b114 vocab=e5d803aa
-/
lemma PartialMap.isOver_toRationalMap_iff_of_isSeparated [X.Over S] [Y.Over S] [IsReduced X]
    [S.IsSeparated] {f : X.PartialMap Y} :
    f.toRationalMap.IsOver S ↔ f.IsOver S := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  obtain ⟨U, hU, hU', H⟩ := f.exists_restrict_isOver (S := S)
  rw [isOver_iff]
  have : IsDominant (X.homOfLE hU') := Opens.isDominant_homOfLE hU _
  exact ext_of_isDominant (ι := X.homOfLE hU') (by simpa using H.1)

section functionField

set_option backward.defeqAttrib.useBackward true in
/-- A rational map restricts to a map from `Spec K(X)`. -/
noncomputable
def RationalMap.fromFunctionField [IrreducibleSpace X] (f : X ⤏ Y) :
    Spec X.functionField ⟶ Y := by
  refine Quotient.lift PartialMap.fromFunctionField ?_ f
  intro f g ⟨W, hW, hWl, hWr, e⟩
  have : f.restrict W hW hWl = g.restrict W hW hWr := by
    ext1
    · rfl
    rw [e]; simp
  rw [← f.fromFunctionField_restrict hW hWl, this, g.fromFunctionField_restrict]

/--
@isnad1 id=eq.0h3v.s5.69cf4ea250b0 from=seed src=0 shape=d59f3166 vocab=5d4c6063
-/
@[simp]
lemma RationalMap.fromFunctionField_toRationalMap [IrreducibleSpace X] (f : X.PartialMap Y) :
    f.toRationalMap.fromFunctionField = f.fromFunctionField := rfl

/--
Given `S`-schemes `X` and `Y` such that `Y` is locally of finite type and `X` is integral,
any `S`-morphism `Spec K(X) ⟶ Y` spreads out to a rational map from `X` to `Y`.
-/
noncomputable
def RationalMap.ofFunctionField [IsIntegral X] [LocallyOfFiniteType sY]
    (f : Spec X.functionField ⟶ Y) (h : f ≫ sY = X.fromSpecStalk _ ≫ sX) : X ⤏ Y :=
  (PartialMap.ofFromSpecStalk sX sY f h).toRationalMap

/--
@isnad1 id=eq.1h6v.s7.1b8ff721fdaa from=seed src=0 shape=b8f917fc vocab=8e695e47
-/
lemma RationalMap.fromFunctionField_ofFunctionField [IsIntegral X] [LocallyOfFiniteType sY]
    (f : Spec X.functionField ⟶ Y) (h : f ≫ sY = X.fromSpecStalk _ ≫ sX) :
    (ofFunctionField sX sY f h).fromFunctionField = f :=
  PartialMap.fromSpecStalkOfMem_ofFromSpecStalk sX sY _ _

lemma RationalMap.eq_of_fromFunctionField_eq [IsIntegral X] (f g : X.RationalMap Y)
    (H : f.fromFunctionField = g.fromFunctionField) : f = g := by
  obtain ⟨f, rfl⟩ := f.exists_rep
  obtain ⟨g, rfl⟩ := g.exists_rep
  refine PartialMap.toRationalMap_eq_iff.mpr ?_
  exact PartialMap.equiv_of_fromSpecStalkOfMem_eq _ _ _ _ H

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Given `S`-schemes `X` and `Y` such that `Y` is locally of finite type and `X` is integral,
`S`-morphisms `Spec K(X) ⟶ Y` correspond bijectively to `S`-rational maps from `X` to `Y`.
-/
noncomputable
def RationalMap.equivFunctionField [IsIntegral X] [LocallyOfFiniteType sY] :
    { f : Spec X.functionField ⟶ Y // f ≫ sY = X.fromSpecStalk _ ≫ sX } ≃
      { f : X ⤏ Y // f.compHom sY = sX.toRationalMap } where
  toFun f := ⟨.ofFunctionField sX sY f f.2, PartialMap.toRationalMap_eq_iff.mpr
      ⟨_, PartialMap.dense_domain _, le_rfl, le_top, by simp [PartialMap.ofFromSpecStalk_comp]⟩⟩
  invFun f := ⟨f.1.fromFunctionField, by
    obtain ⟨f, hf⟩ := f
    obtain ⟨f, rfl⟩ := f.exists_rep
    simpa [fromFunctionField_toRationalMap] using! congr(RationalMap.fromFunctionField $hf)⟩
  left_inv f := Subtype.ext (RationalMap.fromFunctionField_ofFunctionField _ _ _ _)
  right_inv f := Subtype.ext (RationalMap.eq_of_fromFunctionField_eq
      (ofFunctionField sX sY f.1.fromFunctionField _) f
      (RationalMap.fromFunctionField_ofFunctionField _ _ _ _))

/--
Given `S`-schemes `X` and `Y` such that `Y` is locally of finite type and `X` is integral,
`S`-morphisms `Spec K(X) ⟶ Y` correspond bijectively to `S`-rational maps from `X` to `Y`.
-/
noncomputable
def RationalMap.equivFunctionFieldOver [X.Over S] [Y.Over S] [IsIntegral X]
    [LocallyOfFiniteType (Y ↘ S)] :
    { f : Spec X.functionField ⟶ Y // f.IsOver S } ≃ { f : X ⤏ Y // f.IsOver S } :=
  ((Equiv.subtypeEquivProp (by simp only [Hom.isOver_iff]; rfl)).trans
    (RationalMap.equivFunctionField (X ↘ S) (Y ↘ S))).trans
      (Equiv.subtypeEquivProp (by ext f; rw [RationalMap.isOver_iff]))

end functionField

section domain

/-- The domain of definition of a rational map. -/
def RationalMap.domain (f : X ⤏ Y) : X.Opens :=
  sSup { PartialMap.domain g | (g) (_ : g.toRationalMap = f) }

/--
@isnad1 id=le.0h3v.s5.2813c26c3551 from=seed src=0 shape=525ca138 vocab=57e4e6f8
-/
lemma PartialMap.le_domain_toRationalMap (f : X.PartialMap Y) :
    f.domain ≤ f.toRationalMap.domain :=
  le_sSup ⟨f, rfl, rfl⟩

/--
@isnad1 id=iff.0h4v.s7.055b70ecb6e2 from=seed src=0 shape=2d9ce90a vocab=18e0c3d0
-/
lemma RationalMap.mem_domain {f : X ⤏ Y} {x} :
    x ∈ f.domain ↔ ∃ g : X.PartialMap Y, x ∈ g.domain ∧ g.toRationalMap = f :=
  TopologicalSpace.Opens.mem_sSup.trans (by simp [@and_comm (x ∈ _)])

/--
@isnad1 id=dense.0h3v.s5.c00f071f7637 from=seed src=0 shape=bb3d27df vocab=b61f5a7a
-/
lemma RationalMap.dense_domain (f : X ⤏ Y) : Dense (X := X) f.domain :=
  f.inductionOn (fun g ↦ g.dense_domain.mono g.le_domain_toRationalMap)

set_option backward.isDefEq.respectTransparency false in
/-- The open cover of the domain of `f : X ⤏ Y`,
consisting of all the domains of the partial maps in the equivalence class. -/
noncomputable
def RationalMap.openCoverDomain (f : X ⤏ Y) : f.domain.toScheme.OpenCover where
  I₀ := { PartialMap.domain g | (g) (_ : g.toRationalMap = f) }
  X U := U.1.toScheme
  f U := X.homOfLE (le_sSup U.2)
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    use ⟨_, (TopologicalSpace.Opens.mem_sSup.mp x.2).choose_spec.1⟩
    exact ⟨⟨x.1, (TopologicalSpace.Opens.mem_sSup.mp x.2).choose_spec.2⟩, Subtype.ext (by simp)⟩

set_option backward.isDefEq.respectTransparency false in
/-- If `f : X ⤏ Y` is a rational map from a reduced scheme to a separated scheme,
then `f` can be represented as a partial map on its domain of definition. -/
noncomputable
def RationalMap.toPartialMap [IsReduced X] [Y.IsSeparated] (f : X ⤏ Y) : X.PartialMap Y := by
  refine ⟨f.domain, f.dense_domain, f.openCoverDomain.glueMorphisms
    (fun x ↦ (X.isoOfEq x.2.choose_spec.2).inv ≫ x.2.choose.hom) ?_⟩
  intro x y
  let g (x : f.openCoverDomain.I₀) := x.2.choose
  have hg₁ (x) : (g x).toRationalMap = f := x.2.choose_spec.1
  have hg₂ (x) : (g x).domain = x.1 := x.2.choose_spec.2
  refine (cancel_epi (isPullback_opens_inf_le (le_sSup x.2) (le_sSup y.2)).isoPullback.hom).mp ?_
  simp only [openCoverDomain, IsPullback.isoPullback_hom_fst_assoc,
    IsPullback.isoPullback_hom_snd_assoc]
  change _ ≫ _ ≫ (g x).hom = _ ≫ _ ≫ (g y).hom
  simp_rw [← cancel_epi (X.isoOfEq congr($(hg₂ x) ⊓ $(hg₂ y))).hom, ← Category.assoc]
  convert! (PartialMap.equiv_iff_of_isSeparated (S := ⊤_ _) (f := g x) (g := g y)).mp ?_ using 1
  · dsimp; congr 1; simp [g, ← cancel_mono (Opens.ι _)]
  · dsimp; congr 1; simp [g, ← cancel_mono (Opens.ι _)]
  · rw [← PartialMap.toRationalMap_eq_iff, hg₁, hg₁]

set_option backward.defeqAttrib.useBackward true in
/--
@isnad1 id=eq.0h3v.s6.46185264a6e1 from=seed src=0 shape=74cc3df0 vocab=b8eda602
-/
lemma PartialMap.toPartialMap_toRationalMap_restrict [IsReduced X] [Y.IsSeparated]
    (f : X.PartialMap Y) : (f.toRationalMap.toPartialMap.restrict _ f.dense_domain
      f.le_domain_toRationalMap).hom = f.hom := by
  dsimp [RationalMap.toPartialMap]
  refine (f.toRationalMap.openCoverDomain.ι_glueMorphisms _ _ ⟨_, f, rfl, rfl⟩).trans ?_
  generalize_proofs _ _ H _
  have : H.choose = f := (equiv_iff_of_domain_eq_of_isSeparated (S := ⊤_ _) H.choose_spec.2).mp
    (toRationalMap_eq_iff.mp H.choose_spec.1)
  exact ((ext_iff _ _).mp this.symm).choose_spec.symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
@isnad1 id=eq.0h3v.s4.e880399d1ad4 from=seed src=0 shape=8a204f56 vocab=0830f459
-/
@[simp]
lemma RationalMap.toRationalMap_toPartialMap [IsReduced X] [Y.IsSeparated]
    (f : X ⤏ Y) : f.toPartialMap.toRationalMap = f := by
  obtain ⟨f, rfl⟩ := PartialMap.toRationalMap_surjective f
  trans (f.toRationalMap.toPartialMap.restrict _
    f.dense_domain f.le_domain_toRationalMap).toRationalMap
  · simp
  · congr 1
    exact PartialMap.ext _ f rfl (by simpa using f.toPartialMap_toRationalMap_restrict)

instance [IsReduced X] [Y.IsSeparated] [S.IsSeparated] [X.Over S] [Y.Over S]
    (f : X ⤏ Y) [f.IsOver S] : f.toPartialMap.IsOver S := by
  rw [← PartialMap.isOver_toRationalMap_iff_of_isSeparated, f.toRationalMap_toPartialMap]
  infer_instance

end domain

end Scheme

end AlgebraicGeometry
