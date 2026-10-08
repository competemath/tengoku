/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Riccardo Brasca
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Normed.Group.Constructions
public import Tengoku.Seed.Analysis.Normed.Group.Hom
public import Tengoku.Seed.CategoryTheory.ConcreteCategory.Forget
public import Tengoku.Seed.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# The category of seminormed groups

We define `SemiNormedGrp`, the category of seminormed groups and normed group homs between
them, as well as `SemiNormedGrp₁`, the subcategory of norm non-increasing morphisms.
-/

@[expose] public section


noncomputable section

universe u

open CategoryTheory

/-- The category of seminormed abelian groups and bounded group homomorphisms. -/
structure SemiNormedGrp : Type (u + 1) where
  /-- Construct a bundled `SemiNormedGrp` from the underlying type and typeclass. -/
  of ::
  /-- The underlying seminormed abelian group. -/
  carrier : Type u
  [str : SeminormedAddCommGroup carrier]

attribute [instance] SemiNormedGrp.str

namespace SemiNormedGrp

instance : CoeSort SemiNormedGrp Type* where
  coe X := X.carrier

/-- The type of morphisms in `SemiNormedGrp` -/
@[ext]
structure Hom (M N : SemiNormedGrp.{u}) where
  /-- The underlying `NormedAddGroupHom`. -/
  hom' : NormedAddGroupHom M N

instance : LargeCategory.{u} SemiNormedGrp where
  Hom X Y := Hom X Y
  id X := ⟨NormedAddGroupHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory SemiNormedGrp (NormedAddGroupHom · ·) where
  hom f := f.hom'
  ofHom f := ⟨f⟩

/-- Turn a morphism in `SemiNormedGrp` back into a `NormedAddGroupHom`. -/
abbrev Hom.hom {M N : SemiNormedGrp.{u}} (f : Hom M N) :=
  ConcreteCategory.hom (C := SemiNormedGrp) f

/-- Typecheck a `NormedAddGroupHom` as a morphism in `SemiNormedGrp`. -/
abbrev ofHom {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) : of M ⟶ of N :=
  ConcreteCategory.ofHom (C := SemiNormedGrp) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (M N : SemiNormedGrp.{u}) (f : Hom M N) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/
/--
@isnad1 id=eq.1h4v.s7.7a14d0320441 from=seed src=0 shape=2fe9d3b5 vocab=793ea773
-/
@[ext]
lemma ext {M N : SemiNormedGrp} {f₁ f₂ : M ⟶ N} (h : ∀ (x : M), f₁ x = f₂ x) : f₁ = f₂ :=
  ConcreteCategory.ext_apply h

/--
@isnad1 id=eq.0h1v.s4.018478b01d0e from=seed src=0 shape=98150753 vocab=8cbc9ada
-/
@[simp]
lemma hom_id {M : SemiNormedGrp} : (𝟙 M : M ⟶ M).hom = NormedAddGroupHom.id M := rfl

/- Provided for rewriting. -/
/--
@isnad1 id=eq.0h2v.s6.d11d75d5ada2 from=seed src=0 shape=567e892f vocab=f78ba83d
-/
lemma id_apply (M : SemiNormedGrp) (r : M) :
    (𝟙 M : M ⟶ M) r = r := by simp

/--
@isnad1 id=eq.0h5v.s6.0daaaf1b54a5 from=seed src=0 shape=f9bc9902 vocab=b57670c1
-/
@[simp]
lemma hom_comp {M N O : SemiNormedGrp} (f : M ⟶ N) (g : N ⟶ O) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
/--
@isnad1 id=eq.0h6v.s8.227c275ab577 from=seed src=0 shape=f8fbaaa5 vocab=02c0b8aa
-/
lemma comp_apply {M N O : SemiNormedGrp} (f : M ⟶ N) (g : N ⟶ O) (r : M) :
    (f ≫ g) r = g (f r) := by simp

/--
@isnad1 id=eq.1h4v.s5.9e33cdebf504 from=seed src=0 shape=bce286ca vocab=d8d25707
-/
@[ext]
lemma hom_ext {M N : SemiNormedGrp} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

/--
@isnad1 id=eq.0h3v.s5.c77bc27f7035 from=seed src=0 shape=ee82f57b vocab=29ed30bb
-/
@[simp]
lemma hom_ofHom {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) : (ofHom f).hom = f := rfl

/--
@isnad1 id=eq.0h3v.s5.55949af039f2 from=seed src=0 shape=67807d68 vocab=752de0bd
-/
@[simp]
lemma ofHom_hom {M N : SemiNormedGrp} (f : M ⟶ N) :
    ofHom (Hom.hom f) = f := rfl

/--
@isnad1 id=eq.0h1v.s5.7ff25145b43c from=seed src=0 shape=fa1b0b56 vocab=e06c4489
-/
@[simp]
lemma ofHom_id {M : Type u} [SeminormedAddCommGroup M] :
    ofHom (NormedAddGroupHom.id M) = 𝟙 (of M) := rfl

/--
@isnad1 id=eq.0h5v.s6.103d1be5e330 from=seed src=0 shape=17e991ae vocab=cf64c842
-/
@[simp]
lemma ofHom_comp {M N O : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
    [SeminormedAddCommGroup O] (f : NormedAddGroupHom M N) (g : NormedAddGroupHom N O) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

/--
@isnad1 id=eq.0h4v.s7.c26181c7d552 from=seed src=0 shape=c7895988 vocab=e0478a85
-/
lemma ofHom_apply {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) (r : M) : ofHom f r = f r := rfl

/--
@isnad1 id=eq.0h4v.s7.283215a2a9f2 from=seed src=0 shape=a6fcc484 vocab=51868072
-/
lemma inv_hom_apply {M N : SemiNormedGrp} (e : M ≅ N) (r : M) : e.inv (e.hom r) = r := by
  simp

/--
@isnad1 id=eq.0h4v.s7.a183527ac8e4 from=seed src=0 shape=f8bdf8bf vocab=51868072
-/
lemma hom_inv_apply {M N : SemiNormedGrp} (e : M ≅ N) (s : N) : e.hom (e.inv s) = s := by
  simp

/--
@isnad1 id=eq.0h1v.s3.42dd99b73fcc from=seed src=0 shape=62728698 vocab=a1db831f
-/
theorem coe_of (V : Type u) [SeminormedAddCommGroup V] : (SemiNormedGrp.of V : Type u) = V :=
  rfl

/--
@isnad1 id=eq.0h1v.s6.2b88c331617d from=seed src=0 shape=bae0b6c4 vocab=93a48648
-/
theorem coe_id (V : SemiNormedGrp) : (𝟙 V : V → V) = id :=
  rfl

/--
@isnad1 id=eq.0h5v.s8.bd181bc4c16b from=seed src=0 shape=bfb9d4a0 vocab=afb0e36f
-/
theorem coe_comp {M N K : SemiNormedGrp} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : M → K) = g ∘ f :=
  rfl

instance : Inhabited SemiNormedGrp :=
  ⟨of PUnit⟩

instance {M N : SemiNormedGrp} : Zero (M ⟶ N) where
  zero := ofHom 0

/--
@isnad1 id=eq.0h2v.s6.0c89ad158e4e from=seed src=0 shape=43b74054 vocab=d8d25707
-/
@[simp]
theorem hom_zero {V W : SemiNormedGrp} : (0 : V ⟶ W).hom = 0 :=
  rfl

/--
@isnad1 id=eq.0h3v.s7.2ce459d1fa92 from=seed src=0 shape=e6760921 vocab=793ea773
-/
theorem zero_apply {V W : SemiNormedGrp} (x : V) : (0 : V ⟶ W) x = 0 :=
  rfl

instance : Limits.HasZeroMorphisms.{u, u + 1} SemiNormedGrp where

/--
@isnad1 id=iszero.0h1v.s3.6feb36c1af71 from=seed src=0 shape=346eab1f vocab=aac8947f
-/
theorem isZero_of_subsingleton (V : SemiNormedGrp) [Subsingleton V] : Limits.IsZero V := by
  refine ⟨fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩
  · ext x; have : x = 0 := Subsingleton.elim _ _; simp only [this, map_zero]
  · ext; apply Subsingleton.elim

/--
@isnad1 id=haszeroo.0h0v.s1.9f85c208d052 from=seed src=0 shape=49959d42 vocab=0134aade
-/
instance hasZeroObject : Limits.HasZeroObject SemiNormedGrp.{u} :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩

/--
@isnad1 id=isometry.2h3v.s7.056dc8fe36f6 from=seed src=0 shape=83b7269a vocab=935dfd02
-/
theorem iso_isometry_of_normNoninc {V W : SemiNormedGrp} (i : V ≅ W) (h1 : i.hom.hom.NormNoninc)
    (h2 : i.inv.hom.NormNoninc) : Isometry i.hom := by
  apply AddMonoidHomClass.isometry_of_norm
  intro v
  apply le_antisymm (h1 v)
  calc
    ‖v‖ = ‖i.inv (i.hom v)‖ := by rw [← comp_apply, Iso.hom_inv_id, id_apply]
    _ ≤ ‖i.hom v‖ := h2 _

instance Hom.add {M N : SemiNormedGrp} : Add (M ⟶ N) where
  add f g := ofHom (f.hom + g.hom)

/--
@isnad1 id=eq.0h4v.s7.13409325924f from=seed src=0 shape=deacb64a vocab=d6860509
-/
@[simp]
theorem hom_add {V W : SemiNormedGrp} (f g : V ⟶ W) : (f + g).hom = f.hom + g.hom :=
  rfl

instance Hom.neg {M N : SemiNormedGrp} : Neg (M ⟶ N) where
  neg f := ofHom (- f.hom)

/--
@isnad1 id=eq.0h3v.s6.a5ba547ba87a from=seed src=0 shape=7b681a98 vocab=a6bebba4
-/
@[simp]
theorem hom_neg {V W : SemiNormedGrp} (f : V ⟶ W) : (-f).hom = -f.hom :=
  rfl

instance Hom.sub {M N : SemiNormedGrp} : Sub (M ⟶ N) where
  sub f g := ofHom (f.hom - g.hom)

/--
@isnad1 id=eq.0h4v.s7.bb11e3646038 from=seed src=0 shape=deacb64a vocab=903f8ff2
-/
@[simp]
theorem hom_sub {V W : SemiNormedGrp} (f g : V ⟶ W) : (f - g).hom = f.hom - g.hom :=
  rfl

instance Hom.nsmul {M N : SemiNormedGrp} : SMul ℕ (M ⟶ N) where
  smul n f := ofHom (n • f.hom)

/--
@isnad1 id=eq.0h4v.s6.b45595eee027 from=seed src=0 shape=821cd5db vocab=4e17f5c8
-/
@[simp]
theorem hom_nsum {V W : SemiNormedGrp} (n : ℕ) (f : V ⟶ W) : (n • f).hom = n • f.hom :=
  rfl

instance Hom.zsmul {M N : SemiNormedGrp} : SMul ℤ (M ⟶ N) where
  smul n f := ofHom (n • f.hom)

/--
@isnad1 id=eq.0h4v.s6.55805ea03825 from=seed src=0 shape=821cd5db vocab=bc3b090b
-/
@[simp]
theorem hom_zsum {V W : SemiNormedGrp} (n : ℤ) (f : V ⟶ W) : (n • f).hom = n • f.hom :=
  rfl

instance Hom.addCommGroup {V W : SemiNormedGrp} : AddCommGroup (V ⟶ W) :=
  Function.Injective.addCommGroup _ ConcreteCategory.hom_injective rfl (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

end SemiNormedGrp

/-- `SemiNormedGrp₁` is a type synonym for `SemiNormedGrp`,
which we shall equip with the category structure consisting only of the norm non-increasing maps.
-/
structure SemiNormedGrp₁ : Type (u + 1) where
  /-- Construct a bundled `SemiNormedGrp₁` from the underlying type and typeclass. -/
  of ::
  /-- The underlying seminormed abelian group. -/
  carrier : Type u
  [str : SeminormedAddCommGroup carrier]

attribute [instance] SemiNormedGrp₁.str

namespace SemiNormedGrp₁

instance : CoeSort SemiNormedGrp₁ Type* where
  coe X := X.carrier

/-- The type of morphisms in `SemiNormedGrp₁` -/
@[ext]
structure Hom (M N : SemiNormedGrp₁.{u}) where
  /-- The underlying `NormedAddGroupHom`. -/
  hom' : NormedAddGroupHom M N
  normNoninc : hom'.NormNoninc

instance : LargeCategory.{u} SemiNormedGrp₁ where
  Hom := Hom
  id X := ⟨NormedAddGroupHom.id X, NormedAddGroupHom.NormNoninc.id⟩
  comp {_ _ _} f g := ⟨g.1.comp f.1, g.2.comp f.2⟩

instance instFunLike (X Y : SemiNormedGrp₁) :
    FunLike { f : NormedAddGroupHom X Y // f.NormNoninc } X Y where
  coe f := f.1.toFun
  coe_injective _ _ h := Subtype.val_inj.mp (NormedAddGroupHom.coe_injective h)

instance : ConcreteCategory SemiNormedGrp₁
    fun X Y => { f : NormedAddGroupHom X Y // f.NormNoninc } where
  hom f := ⟨f.1, f.2⟩
  ofHom f := ⟨f.1, f.2⟩

instance (X Y : SemiNormedGrp₁) :
    AddMonoidHomClass { f : NormedAddGroupHom X Y // f.NormNoninc } X Y where
  map_add f := map_add f.1
  map_zero f := map_zero f.1

/-- Turn a morphism in `SemiNormedGrp₁` back into a norm-nonincreasing `NormedAddGroupHom`. -/
abbrev Hom.hom {M N : SemiNormedGrp₁.{u}} (f : Hom M N) :=
  ConcreteCategory.hom (C := SemiNormedGrp₁) f

/-- Promote a `NormedAddGroupHom` to a morphism in `SemiNormedGrp₁`. -/
abbrev mkHom {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) (i : f.NormNoninc) :
    SemiNormedGrp₁.of M ⟶ SemiNormedGrp₁.of N :=
  ConcreteCategory.ofHom ⟨f, i⟩

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (M N : SemiNormedGrp₁.{u}) (f : Hom M N) : NormedAddGroupHom M N :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

instance (X Y : SemiNormedGrp₁) : CoeFun (X ⟶ Y) (fun _ => X → Y) where
  coe f := f.hom.1

/--
@isnad1 id=eq.1h4v.s7.501af3e9f1b9 from=seed src=0 shape=34d00c09 vocab=68dcce4c
-/
theorem mkHom_apply {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) (i : f.NormNoninc) (x) :
    mkHom f i x = f x :=
  rfl

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/
/--
@isnad1 id=eq.1h4v.s7.64296374d6eb from=seed src=0 shape=b1e711ea vocab=568c9a4f
-/
@[ext]
lemma ext {M N : SemiNormedGrp₁} {f₁ f₂ : M ⟶ N} (h : ∀ (x : M), f₁ x = f₂ x) : f₁ = f₂ :=
  ConcreteCategory.ext_apply h

/--
@isnad1 id=eq.0h1v.s5.7c8388095878 from=seed src=0 shape=1b4858d7 vocab=22901d42
-/
@[simp]
lemma hom_id {M : SemiNormedGrp₁} : (𝟙 M : M ⟶ M).hom = NormedAddGroupHom.id M := rfl

/- Provided for rewriting. -/
/--
@isnad1 id=eq.0h2v.s6.4e781d85a963 from=seed src=0 shape=918c3b59 vocab=dd709682
-/
lemma id_apply (M : SemiNormedGrp₁) (r : M) :
    (𝟙 M : M ⟶ M) r = r := by simp

/--
@isnad1 id=eq.0h5v.s7.a60a4a66adc2 from=seed src=0 shape=ce2a8f6a vocab=479af620
-/
@[simp]
lemma hom_comp {M N O : SemiNormedGrp₁} (f : M ⟶ N) (g : N ⟶ O) :
    (f ≫ g).hom.1 = g.hom.1.comp f.hom.1 := rfl

/- Provided for rewriting. -/
/--
@isnad1 id=eq.0h6v.s7.ba89f0c58b3b from=seed src=0 shape=47bf4671 vocab=554a8959
-/
lemma comp_apply {M N O : SemiNormedGrp₁} (f : M ⟶ N) (g : N ⟶ O) (r : M) :
    (f ≫ g) r = g (f r) := by simp

/--
@isnad1 id=eq.1h4v.s6.aacc929856f2 from=seed src=0 shape=63ee421a vocab=bafa76e1
-/
@[ext]
lemma hom_ext {M N : SemiNormedGrp₁} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g :=
  Hom.ext (congr_arg Subtype.val hf)

/--
@isnad1 id=eq.1h3v.s6.ad4be67e04f6 from=seed src=0 shape=5bc27328 vocab=2d1043cc
-/
@[simp]
lemma hom_mkHom {M N : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) (hf : f.NormNoninc) : (mkHom f hf).hom = f := rfl

/--
@isnad1 id=eq.0h3v.s6.c4ec97eede86 from=seed src=0 shape=301886d2 vocab=4563f732
-/
@[simp]
lemma mkHom_hom {M N : SemiNormedGrp₁} (f : M ⟶ N) :
    mkHom (Hom.hom f) f.normNoninc = f := rfl

/--
@isnad1 id=eq.0h1v.s5.26893a657ca7 from=seed src=0 shape=677082c5 vocab=85e11ede
-/
@[simp]
lemma mkHom_id {M : Type u} [SeminormedAddCommGroup M] :
    mkHom (NormedAddGroupHom.id M) NormedAddGroupHom.NormNoninc.id = 𝟙 (of M) := rfl

/--
@isnad1 id=eq.3h5v.s6.e2ccfb001462 from=seed src=0 shape=3bc0ec87 vocab=61472645
-/
@[simp]
lemma mkHom_comp {M N O : Type u} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
    [SeminormedAddCommGroup O] (f : NormedAddGroupHom M N) (g : NormedAddGroupHom N O)
    (hf : f.NormNoninc) (hg : g.NormNoninc) (hgf : (g.comp f).NormNoninc) :
    mkHom (g.comp f) hgf = mkHom f hf ≫ mkHom g hg :=
  rfl

/--
@isnad1 id=eq.0h4v.s7.a92c584f48b9 from=seed src=0 shape=d6090cf8 vocab=0563d2fc
-/
@[simp]
lemma inv_hom_apply {M N : SemiNormedGrp₁} (e : M ≅ N) (r : M) : e.inv (e.hom r) = r := by
  rw [← comp_apply]
  simp

/--
@isnad1 id=eq.0h4v.s7.1b6b135df0cc from=seed src=0 shape=93f37ed1 vocab=0563d2fc
-/
@[simp]
lemma hom_inv_apply {M N : SemiNormedGrp₁} (e : M ≅ N) (s : N) : e.hom (e.inv s) = s := by
  rw [← comp_apply]
  simp

instance (M : SemiNormedGrp₁) : SeminormedAddCommGroup M :=
  M.str

/-- Promote an isomorphism in `SemiNormedGrp` to an isomorphism in `SemiNormedGrp₁`. -/
@[simps]
def mkIso {M N : SemiNormedGrp} (f : M ≅ N) (i : f.hom.hom.NormNoninc) (i' : f.inv.hom.NormNoninc) :
    SemiNormedGrp₁.of M ≅ SemiNormedGrp₁.of N where
  hom := mkHom f.hom.hom i
  inv := mkHom f.inv.hom i'

instance : HasForget₂ SemiNormedGrp₁ SemiNormedGrp where
  forget₂ :=
    { obj := fun X => SemiNormedGrp.of X
      map := fun f => SemiNormedGrp.ofHom f.1 }

/--
@isnad1 id=eq.0h1v.s3.560b17cdb82f from=seed src=0 shape=62728698 vocab=45c15dde
-/
theorem coe_of (V : Type u) [SeminormedAddCommGroup V] : (SemiNormedGrp₁.of V : Type u) = V :=
  rfl

/--
@isnad1 id=eq.0h1v.s6.43cea8f6c821 from=seed src=0 shape=e8c67055 vocab=4bd6d53d
-/
theorem coe_id (V : SemiNormedGrp₁) : ⇑(𝟙 V) = id :=
  rfl

/--
@isnad1 id=eq.0h5v.s7.1b10b0644212 from=seed src=0 shape=54a1db15 vocab=880c1823
-/
theorem coe_comp {M N K : SemiNormedGrp₁} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : M → K) = g ∘ f :=
  rfl

instance : Inhabited SemiNormedGrp₁ :=
  ⟨of PUnit⟩

instance (X Y : SemiNormedGrp₁) : Zero (X ⟶ Y) where
  zero := ⟨0, NormedAddGroupHom.NormNoninc.zero⟩

/--
@isnad1 id=eq.0h3v.s6.def1078b1bab from=seed src=0 shape=b40cc0ad vocab=568c9a4f
-/
@[simp]
theorem zero_apply {V W : SemiNormedGrp₁} (x : V) : (0 : V ⟶ W) x = 0 :=
  rfl

instance : Limits.HasZeroMorphisms.{u, u + 1} SemiNormedGrp₁ where

/--
@isnad1 id=iszero.0h1v.s3.ad18586747e8 from=seed src=0 shape=346eab1f vocab=84cd639f
-/
theorem isZero_of_subsingleton (V : SemiNormedGrp₁) [Subsingleton V] : Limits.IsZero V := by
  refine ⟨fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩
  · ext x; have : x = 0 := Subsingleton.elim _ _; simp only [this, map_zero]
  · ext; apply Subsingleton.elim

/--
@isnad1 id=haszeroo.0h0v.s1.b60e2c5b10a4 from=seed src=0 shape=49959d42 vocab=1b97360c
-/
instance hasZeroObject : Limits.HasZeroObject SemiNormedGrp₁.{u} :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩

/--
@isnad1 id=isometry.0h3v.s6.d4f12aa53de5 from=seed src=0 shape=9b01aab5 vocab=ac005b0a
-/
theorem iso_isometry {V W : SemiNormedGrp₁} (i : V ≅ W) : Isometry i.hom := by
  change Isometry (⟨⟨i.hom, map_zero _⟩, fun _ _ => map_add _ _ _⟩ : V →+ W)
  refine AddMonoidHomClass.isometry_of_norm _ ?_
  intro v
  apply le_antisymm (i.hom.2 v)
  calc
    ‖v‖ = ‖i.inv (i.hom v)‖ := by rw [← comp_apply, Iso.hom_inv_id, id_apply]
    _ ≤ ‖i.hom v‖ := i.inv.2 _

end SemiNormedGrp₁
