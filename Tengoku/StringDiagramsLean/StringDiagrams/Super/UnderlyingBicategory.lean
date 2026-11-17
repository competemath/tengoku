import Tengoku.StringDiagramsLean.StringDiagrams.Super.Underlying
import Tengoku.StringDiagramsLean.StringDiagrams.Super.Bicategory

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The underlying bicategory of a 2-supercategory

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Definition 1.1(v) and Definition 2.2(i): the *underlying 2-category* of a 2-supercategory `𝔄`
has the same objects and 1-morphisms, and only the even 2-morphisms. On even 2-morphisms the
super interchange law is the ordinary interchange law, so this is a bicategory in the sense of
Mathlib (`Underlying2.instBicategory`), whose hom categories are the underlying categories
`Underlying R (a ⟶ b)` of the morphism supercategories.

We use it to transport Mathlib's coherence lemmas, which only involve the even coherence maps,
back to the 2-supercategory (`TwoSupercategory.unitors_equal`,
`TwoSupercategory.leftUnitor_comp`, `TwoSupercategory.rightUnitor_comp`, …). We also record the
naturality of the associator and unitors with respect to arbitrary (not necessarily even)
2-morphisms, which follows directly from the axioms.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory BicategoryStruct

universe w v u w₁

/-- The underlying bicategory of a 2-supercategory (Brundan–Ellis, Definition 1.1(v) applied
to the morphism supercategories): the same objects, 1-morphisms `Underlying R (a ⟶ b)`, and
even 2-morphisms.-/
@[ext]
structure Underlying2 (R : Type w₁) (B : Type u) where
  /-- The object of `B`.-/
  obj : B

namespace Underlying2

variable {R : Type w₁} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

/-- The bicategory of even 2-morphisms.-/
instance instBicategory : Bicategory (Underlying2 R B) where
  Hom a b := Underlying R (a.obj ⟶ b.obj)
  id a := ⟨𝟙 a.obj⟩
  comp f g := ⟨f.obj ≫ g.obj⟩
  homCategory _ _ := inferInstance
  whiskerLeft f _ _ η := ⟨f.obj ◁ η.1, TwoSupercategory.whiskerLeft_mem f.obj η.2⟩
  whiskerRight η h := ⟨η.1 ▷ h.obj, TwoSupercategory.whiskerRight_mem h.obj η.2⟩
  associator f g h := Underlying.isoMk (associator f.obj g.obj h.obj)
    (TwoSupercategory.associator_hom_mem _ _ _)
  leftUnitor f := Underlying.isoMk (leftUnitor f.obj) (TwoSupercategory.leftUnitor_hom_mem _)
  rightUnitor f := Underlying.isoMk (rightUnitor f.obj) (TwoSupercategory.rightUnitor_hom_mem _)
  whiskerLeft_id f g := Subtype.ext (TwoSupercategory.whiskerLeft_id (R := R) f.obj g.obj)
  whiskerLeft_comp f _ _ _ η θ :=
    Subtype.ext (TwoSupercategory.whiskerLeft_comp (R := R) f.obj η.1 θ.1)
  id_whiskerLeft η := Subtype.ext (TwoSupercategory.id_whiskerLeft (R := R) η.1)
  comp_whiskerLeft f g _ _ η :=
    Subtype.ext (TwoSupercategory.comp_whiskerLeft (R := R) f.obj g.obj η.1)
  id_whiskerRight f g := Subtype.ext (TwoSupercategory.id_whiskerRight (R := R) f.obj g.obj)
  comp_whiskerRight η θ i :=
    Subtype.ext (TwoSupercategory.comp_whiskerRight (R := R) η.1 θ.1 i.obj)
  whiskerRight_id η := Subtype.ext (TwoSupercategory.whiskerRight_id (R := R) η.1)
  whiskerRight_comp η g h :=
    Subtype.ext (TwoSupercategory.whiskerRight_comp (R := R) η.1 g.obj h.obj)
  whisker_assoc f _ _ η h :=
    Subtype.ext (TwoSupercategory.whisker_assoc (R := R) f.obj η.1 h.obj)
  whisker_exchange η θ := Subtype.ext (by
    have := TwoSupercategory.super_interchange (R := R) η.2 θ.2
    rw [koszulSign_zero_left, one_smul] at this
    exact this.symm)
  pentagon f g h i := Subtype.ext (TwoSupercategory.pentagon (R := R) f.obj g.obj h.obj i.obj)
  triangle f g := Subtype.ext (TwoSupercategory.triangle (R := R) f.obj g.obj)

/-- A 1-morphism of `B`, as a 1-morphism of the underlying bicategory.-/
def hom1 {a b : B} (f : a ⟶ b) : (⟨a⟩ : Underlying2 R B) ⟶ ⟨b⟩ := ⟨f⟩

section Simp

variable {a b c d : Underlying2 R B}

/--
@isnad1 id=eq.0h3v.s7.b09cc7caca47 from=translated src=- shape=ab0fb58e vocab=cb9da1f3
-/
@[simp] theorem id_obj (a : Underlying2 R B) : (𝟙 a : a ⟶ a).obj = 𝟙 a.obj := rfl

/--
@isnad1 id=eq.0h7v.s8.5fe64594f9d7 from=translated src=- shape=46f735e2 vocab=5e1bd32d
-/
@[simp] theorem comp_obj (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).obj = f.obj ≫ g.obj := rfl

/--
@isnad1 id=eq.0h9v.s12.0b99baea828a from=translated src=- shape=6afe6832 vocab=402fd620
-/
@[simp] theorem comp₂_val {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) : (η ≫ θ).1 = η.1 ≫ θ.1 :=
  rfl

/--
@isnad1 id=eq.0h5v.s10.8412cc43c4e6 from=translated src=- shape=14829ed6 vocab=9033147b
-/
@[simp] theorem id₂_val (f : a ⟶ b) : (𝟙 f : f ⟶ f).1 = 𝟙 f.obj := rfl

/--
@isnad1 id=eq.0h5v.s7.dc457268c6c6 from=translated src=- shape=396fe219 vocab=00ba2177
-/
@[simp] theorem hom1_obj {a b : B} (f : a ⟶ b) : (hom1 (R := R) f).obj = f := rfl

/--
@isnad1 id=eq.0h9v.s12.4d44464526b0 from=translated src=- shape=a2c88a85 vocab=4b2e5d8a
-/
@[simp] theorem whiskerLeft_val (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    (Bicategory.whiskerLeft f η).1 = f.obj ◁ η.1 := rfl

/--
@isnad1 id=eq.0h9v.s12.282503d0eefc from=translated src=- shape=5dd72e41 vocab=b4c9ce2f
-/
@[simp] theorem whiskerRight_val {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    (Bicategory.whiskerRight η h).1 = η.1 ▷ h.obj := rfl

/--
@isnad1 id=eq.0h9v.s11.4d00adce741d from=translated src=- shape=2a1e30d2 vocab=67b5b5a6
-/
@[simp] theorem associator_hom_val (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (Bicategory.associator f g h).hom.1 = (associator f.obj g.obj h.obj).hom := rfl

/--
@isnad1 id=eq.0h9v.s11.39da198f5127 from=translated src=- shape=fc85d006 vocab=c06c7d82
-/
@[simp] theorem associator_inv_val (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (Bicategory.associator f g h).inv.1 = (associator f.obj g.obj h.obj).inv := rfl

/--
@isnad1 id=eq.0h5v.s11.69f0cea709df from=translated src=- shape=74ff4964 vocab=e6972aa7
-/
@[simp] theorem leftUnitor_hom_val (f : a ⟶ b) :
    (Bicategory.leftUnitor f).hom.1 = (leftUnitor f.obj).hom := rfl

/--
@isnad1 id=eq.0h5v.s11.b8d3c9c4c2df from=translated src=- shape=a17e163f vocab=dcd5c208
-/
@[simp] theorem leftUnitor_inv_val (f : a ⟶ b) :
    (Bicategory.leftUnitor f).inv.1 = (leftUnitor f.obj).inv := rfl

/--
@isnad1 id=eq.0h5v.s11.dc1da8f5acc8 from=translated src=- shape=5e2519b3 vocab=c301fc38
-/
@[simp] theorem rightUnitor_hom_val (f : a ⟶ b) :
    (Bicategory.rightUnitor f).hom.1 = (rightUnitor f.obj).hom := rfl

/--
@isnad1 id=eq.0h5v.s11.a3d45b2da583 from=translated src=- shape=2d5b8be6 vocab=6f9b4d81
-/
@[simp] theorem rightUnitor_inv_val (f : a ⟶ b) :
    (Bicategory.rightUnitor f).inv.1 = (rightUnitor f.obj).inv := rfl

end Simp

end Underlying2

/-! ## Coherence lemmas for 2-supercategories -/

namespace TwoSupercategory

variable {R : Type w₁} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
  {a b c d e : B}

/-! ### Naturality of the coherence maps (for all 2-morphisms) -/

section Naturality

variable (R)
include R

/--
@isnad1 id=eq.0h11v.s9.b48637ec5674 from=translated src=- shape=9615c6e5 vocab=7695120e
-/
@[reassoc]
theorem associator_naturality_left {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) :
    η ▷ g ▷ h ≫ (associator f' g h).hom = (associator f g h).hom ≫ η ▷ (g ≫ h) := by
  rw [whiskerRight_comp (R := R)]; simp

/--
@isnad1 id=eq.0h11v.s9.a58432d168f7 from=translated src=- shape=7a4bcdee vocab=9a131205
-/
@[reassoc]
theorem associator_inv_naturality_left {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) :
    η ▷ (g ≫ h) ≫ (associator f' g h).inv = (associator f g h).inv ≫ η ▷ g ▷ h := by
  rw [whiskerRight_comp (R := R)]; simp

/--
@isnad1 id=eq.0h11v.s9.d88c670b2cec from=translated src=- shape=277852e2 vocab=698a92d1
-/
@[reassoc]
theorem associator_naturality_middle (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d) :
    (f ◁ η) ▷ h ≫ (associator f g' h).hom = (associator f g h).hom ≫ f ◁ (η ▷ h) := by
  rw [whisker_assoc (R := R)]; simp

/--
@isnad1 id=eq.0h11v.s9.8277f5f93bee from=translated src=- shape=a4efc1a5 vocab=353f1058
-/
@[reassoc]
theorem associator_inv_naturality_middle (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g')
    (h : c ⟶ d) :
    f ◁ (η ▷ h) ≫ (associator f g' h).inv = (associator f g h).inv ≫ (f ◁ η) ▷ h := by
  rw [whisker_assoc (R := R)]; simp

/--
@isnad1 id=eq.0h11v.s9.da60545ee8e9 from=translated src=- shape=6c9733f8 vocab=a56396c6
-/
@[reassoc]
theorem associator_naturality_right (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h') :
    (f ≫ g) ◁ η ≫ (associator f g h').hom = (associator f g h).hom ≫ f ◁ g ◁ η := by
  rw [comp_whiskerLeft (R := R)]; simp

/--
@isnad1 id=eq.0h11v.s9.e4373b4a045d from=translated src=- shape=47a9566c vocab=aee7021a
-/
@[reassoc]
theorem associator_inv_naturality_right (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d}
    (η : h ⟶ h') :
    f ◁ g ◁ η ≫ (associator f g h').inv = (associator f g h).inv ≫ (f ≫ g) ◁ η := by
  rw [comp_whiskerLeft (R := R)]; simp

/--
@isnad1 id=eq.0h7v.s8.c642407434ed from=translated src=- shape=28c0ec74 vocab=cdf2b7d6
-/
@[reassoc]
theorem leftUnitor_naturality {f g : a ⟶ b} (η : f ⟶ g) :
    𝟙 a ◁ η ≫ (leftUnitor g).hom = (leftUnitor f).hom ≫ η := by
  rw [id_whiskerLeft (R := R)]; simp

/--
@isnad1 id=eq.0h7v.s8.f7161d93dd34 from=translated src=- shape=e167bbe6 vocab=7cd06b75
-/
@[reassoc]
theorem leftUnitor_inv_naturality {f g : a ⟶ b} (η : f ⟶ g) :
    η ≫ (leftUnitor g).inv = (leftUnitor f).inv ≫ 𝟙 a ◁ η := by
  rw [id_whiskerLeft (R := R)]; simp

/--
@isnad1 id=eq.0h7v.s8.74506de20c7d from=translated src=- shape=930a5b69 vocab=d56078ed
-/
@[reassoc]
theorem rightUnitor_naturality {f g : a ⟶ b} (η : f ⟶ g) :
    η ▷ 𝟙 b ≫ (rightUnitor g).hom = (rightUnitor f).hom ≫ η := by
  rw [whiskerRight_id (R := R)]; simp

/--
@isnad1 id=eq.0h7v.s8.ed706b562f76 from=translated src=- shape=e5b1cf75 vocab=ae0d79f7
-/
@[reassoc]
theorem rightUnitor_inv_naturality {f g : a ⟶ b} (η : f ⟶ g) :
    η ≫ (rightUnitor g).inv = (rightUnitor f).inv ≫ η ▷ 𝟙 b := by
  rw [whiskerRight_id (R := R)]; simp

/--
@isnad1 id=eq.0h9v.s8.993e82923237 from=translated src=- shape=00936224 vocab=8d54e618
-/
@[reassoc (attr := simp)] theorem whiskerLeft_hom_inv (f : a ⟶ b) {g h : b ⟶ c} (e : g ≅ h) :
    f ◁ e.hom ≫ f ◁ e.inv = 𝟙 (f ≫ g) := by
  rw [← whiskerLeft_comp (R := R), e.hom_inv_id, whiskerLeft_id (R := R)]

/--
@isnad1 id=eq.0h9v.s8.a84f673b5b14 from=translated src=- shape=6256e262 vocab=8d54e618
-/
@[reassoc (attr := simp)] theorem whiskerLeft_inv_hom (f : a ⟶ b) {g h : b ⟶ c} (e : g ≅ h) :
    f ◁ e.inv ≫ f ◁ e.hom = 𝟙 (f ≫ h) := by
  rw [← whiskerLeft_comp (R := R), e.inv_hom_id, whiskerLeft_id (R := R)]

/--
@isnad1 id=eq.0h9v.s8.37e85e394bc4 from=translated src=- shape=2659fb14 vocab=ce45f1a9
-/
@[reassoc (attr := simp)] theorem hom_inv_whiskerRight {f g : a ⟶ b} (e : f ≅ g) (h : b ⟶ c) :
    e.hom ▷ h ≫ e.inv ▷ h = 𝟙 (f ≫ h) := by
  rw [← comp_whiskerRight (R := R), e.hom_inv_id, id_whiskerRight (R := R)]

/--
@isnad1 id=eq.0h9v.s8.11e868df9883 from=translated src=- shape=eeb5dc76 vocab=ce45f1a9
-/
@[reassoc (attr := simp)] theorem inv_hom_whiskerRight {f g : a ⟶ b} (e : f ≅ g) (h : b ⟶ c) :
    e.inv ▷ h ≫ e.hom ▷ h = 𝟙 (g ≫ h) := by
  rw [← comp_whiskerRight (R := R), e.inv_hom_id, id_whiskerRight (R := R)]

/--
@isnad1 id=eq.0h8v.s8.1ae166655fab from=translated src=- shape=cf375404 vocab=b9d45931
-/
@[simp] theorem whiskerLeft_zero (f : a ⟶ b) (g h : b ⟶ c) : f ◁ (0 : g ⟶ h) = 0 := by
  rw [← zero_smul R (0 : g ⟶ h), whiskerLeft_smul, zero_smul]

/--
@isnad1 id=eq.0h8v.s8.d08f3e7e4b3e from=translated src=- shape=26cd5b89 vocab=ec962d1c
-/
@[simp] theorem zero_whiskerRight (f g : a ⟶ b) (h : b ⟶ c) : (0 : f ⟶ g) ▷ h = 0 := by
  rw [← zero_smul R (0 : f ⟶ g), smul_whiskerRight, zero_smul]

/--
@isnad1 id=eq.0h9v.s9.097b78891766 from=translated src=- shape=7b22a986 vocab=172c30e1
-/
@[simp] theorem whiskerLeft_neg (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) : f ◁ (-η) = -(f ◁ η) := by
  rw [← neg_one_smul R η, whiskerLeft_smul, neg_one_smul]

/--
@isnad1 id=eq.0h9v.s9.0c47c9a20ead from=translated src=- shape=5e93bc8b vocab=7a6653f9
-/
@[simp] theorem neg_whiskerRight {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) : (-η) ▷ h = -(η ▷ h) := by
  rw [← neg_one_smul R η, smul_whiskerRight, neg_one_smul]

/--
@isnad1 id=eq.0h10v.s9.afb2e5690914 from=translated src=- shape=8855e537 vocab=c2390f69
-/
theorem whiskerLeft_zsmul (f : a ⟶ b) {g h : b ⟶ c} (n : ℤ) (η : g ⟶ h) :
    f ◁ (n • η) = n • (f ◁ η) := by
  rw [← Int.cast_smul_eq_zsmul R, whiskerLeft_smul, Int.cast_smul_eq_zsmul]

/--
@isnad1 id=eq.0h10v.s9.9445d50b37bb from=translated src=- shape=c1d45083 vocab=7cc8c80e
-/
theorem zsmul_whiskerRight {f g : a ⟶ b} (n : ℤ) (η : f ⟶ g) (h : b ⟶ c) :
    (n • η) ▷ h = n • (η ▷ h) := by
  rw [← Int.cast_smul_eq_zsmul R, smul_whiskerRight, Int.cast_smul_eq_zsmul]

end Naturality

variable (R) in
include R in
/--
@isnad1 id=eq.0h11v.s8.ffb2d94f5893 from=translated src=- shape=31cb02e5 vocab=b9d45931
-/
@[reassoc]
theorem whiskerLeft_comp' (f : a ⟶ b) {g h i : b ⟶ c} (η : g ⟶ h) (θ : h ⟶ i) :
    f ◁ (η ≫ θ) = f ◁ η ≫ f ◁ θ :=
  whiskerLeft_comp (R := R) f η θ

variable (R) in
include R in
/--
@isnad1 id=eq.0h11v.s8.f5b7d4dcaef1 from=translated src=- shape=e600dcbd vocab=ec962d1c
-/
@[reassoc]
theorem comp_whiskerRight' {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (i : b ⟶ c) :
    (η ≫ θ) ▷ i = η ▷ i ≫ θ ▷ i :=
  comp_whiskerRight (R := R) η θ i

/-- The super interchange law, precomposed form.
@isnad1 id=eq.2h15v.s10.4d0e7a0675a2 from=translated src=- shape=6611ae46 vocab=7f5f2066
-/
theorem super_interchange_assoc {f g : a ⟶ b} {h i : b ⟶ c} {p q : ZMod 2} {η : f ⟶ g}
    {θ : h ⟶ i} (hη : η ∈ parity (R := R) f g p) (hθ : θ ∈ parity (R := R) h i q) {k : a ⟶ c}
    (ι : g ≫ i ⟶ k) :
    η ▷ h ≫ g ◁ θ ≫ ι = koszulSign p q • (f ◁ θ ≫ η ▷ i ≫ ι) := by
  rw [← Category.assoc, super_interchange hη hθ, Linear.smul_comp, Category.assoc]

/-- The super interchange law for an even 2-morphism on the left.
@isnad1 id=eq.1h11v.s9.ea7d3f7f0fe1 from=translated src=- shape=854f8f87 vocab=b29241f7
-/
@[reassoc]
theorem whisker_exchange_of_even_left {f g : a ⟶ b} {h i : b ⟶ c} {η : f ⟶ g}
    (hη : η ∈ parity (R := R) f g 0) (θ : h ⟶ i) :
    η ▷ h ≫ g ◁ θ = f ◁ θ ≫ η ▷ i := by
  refine induction_on (R := R) θ (by simp [whiskerLeft_zero R])
    (fun q θ hθ => ?_) (fun θ θ' h h' => ?_)
  · rw [super_interchange hη hθ, koszulSign_zero_left, one_smul]
  · rw [whiskerLeft_add (R := R), whiskerLeft_add (R := R), Preadditive.comp_add,
      Preadditive.add_comp, h, h']

/-- The super interchange law for an even 2-morphism on the right.
@isnad1 id=eq.1h11v.s9.f05830a62c70 from=translated src=- shape=574437f0 vocab=b29241f7
-/
@[reassoc]
theorem whisker_exchange_of_even_right {f g : a ⟶ b} {h i : b ⟶ c} (η : f ⟶ g) {θ : h ⟶ i}
    (hθ : θ ∈ parity (R := R) h i 0) :
    η ▷ h ≫ g ◁ θ = f ◁ θ ≫ η ▷ i := by
  refine induction_on (R := R) η (by simp [zero_whiskerRight R])
    (fun q η hη => ?_) (fun η η' h h' => ?_)
  · rw [super_interchange hη hθ, koszulSign_zero_right, one_smul]
  · rw [add_whiskerRight (R := R), add_whiskerRight (R := R), Preadditive.comp_add,
      Preadditive.add_comp, h, h']

/-- Left whiskering of an isomorphism of 1-morphisms.-/
@[simps]
def whiskerLeftIso (f : a ⟶ b) {g h : b ⟶ c} (e : g ≅ h) : f ≫ g ≅ f ≫ h where
  hom := f ◁ e.hom
  inv := f ◁ e.inv
  hom_inv_id := whiskerLeft_hom_inv R f e
  inv_hom_id := whiskerLeft_inv_hom R f e

/-- Right whiskering of an isomorphism of 1-morphisms.-/
@[simps]
def whiskerRightIso {f g : a ⟶ b} (e : f ≅ g) (h : b ⟶ c) : f ≫ h ≅ g ≫ h where
  hom := e.hom ▷ h
  inv := e.inv ▷ h
  hom_inv_id := hom_inv_whiskerRight R e h
  inv_hom_id := inv_hom_whiskerRight R e h

/-! ### Transported coherence lemmas -/

variable (R) in
include R in
/--
@isnad1 id=eq.0h3v.s8.d261256b3a77 from=translated src=- shape=d3388d5b vocab=ad4737bd
-/
@[reassoc]
theorem unitors_equal (a : B) : (leftUnitor (𝟙 a)).hom = (rightUnitor (𝟙 a)).hom :=
  congrArg Subtype.val (Bicategory.unitors_equal (B := Underlying2 R B) (a := ⟨a⟩))

variable (R) in
include R in
/--
@isnad1 id=eq.0h3v.s8.c47078ac428e from=translated src=- shape=3e09171d vocab=ffc44ff4
-/
@[reassoc]
theorem unitors_inv_equal (a : B) : (leftUnitor (𝟙 a)).inv = (rightUnitor (𝟙 a)).inv :=
  congrArg Subtype.val (Bicategory.unitors_inv_equal (B := Underlying2 R B) (a := ⟨a⟩))

variable (R) in
include R in
/--
@isnad1 id=eq.0h7v.s8.373b2d71c73f from=translated src=- shape=9aeb2f1a vocab=149045f2
-/
@[reassoc]
theorem leftUnitor_comp (f : a ⟶ b) (g : b ⟶ c) :
    (leftUnitor (f ≫ g)).hom = (associator (𝟙 a) f g).inv ≫ (leftUnitor f).hom ▷ g :=
  congrArg Subtype.val
    (Bicategory.leftUnitor_comp (B := Underlying2 R B) (a := ⟨a⟩) (b := ⟨b⟩) (c := ⟨c⟩) (Underlying2.hom1 f) (Underlying2.hom1 g))

variable (R) in
include R in
/--
@isnad1 id=eq.0h7v.s8.ba49e3e63fe1 from=translated src=- shape=52f51b62 vocab=149045f2
-/
@[reassoc]
theorem leftUnitor_comp_inv (f : a ⟶ b) (g : b ⟶ c) :
    (leftUnitor (f ≫ g)).inv = (leftUnitor f).inv ▷ g ≫ (associator (𝟙 a) f g).hom :=
  congrArg Subtype.val
    (Bicategory.leftUnitor_comp_inv (B := Underlying2 R B) (a := ⟨a⟩) (b := ⟨b⟩) (c := ⟨c⟩)
      (Underlying2.hom1 f) (Underlying2.hom1 g))

variable (R) in
include R in
/--
@isnad1 id=eq.0h7v.s8.cfc2910859ff from=translated src=- shape=edb2f825 vocab=9730e5f4
-/
@[reassoc]
theorem rightUnitor_comp (f : a ⟶ b) (g : b ⟶ c) :
    (rightUnitor (f ≫ g)).hom = (associator f g (𝟙 c)).hom ≫ f ◁ (rightUnitor g).hom :=
  congrArg Subtype.val
    (Bicategory.rightUnitor_comp (B := Underlying2 R B) (a := ⟨a⟩) (b := ⟨b⟩) (c := ⟨c⟩)
      (Underlying2.hom1 f) (Underlying2.hom1 g))

variable (R) in
include R in
/--
@isnad1 id=eq.0h7v.s8.c28ff3c6fd3a from=translated src=- shape=825e9dd5 vocab=25d668e9
-/
@[reassoc]
theorem rightUnitor_comp_inv (f : a ⟶ b) (g : b ⟶ c) :
    (rightUnitor (f ≫ g)).inv = f ◁ (rightUnitor g).inv ≫ (associator f g (𝟙 c)).inv :=
  congrArg Subtype.val
    (Bicategory.rightUnitor_comp_inv (B := Underlying2 R B) (a := ⟨a⟩) (b := ⟨b⟩) (c := ⟨c⟩)
      (Underlying2.hom1 f) (Underlying2.hom1 g))

variable (R) in
include R in
/--
@isnad1 id=eq.0h7v.s8.1da39829e83c from=translated src=- shape=370e3730 vocab=2978b6f3
-/
@[reassoc]
theorem leftUnitor_whiskerRight (f : a ⟶ b) (g : b ⟶ c) :
    (leftUnitor f).hom ▷ g = (associator (𝟙 a) f g).hom ≫ (leftUnitor (f ≫ g)).hom :=
  congrArg Subtype.val
    (Bicategory.leftUnitor_whiskerRight (B := Underlying2 R B) (a := ⟨a⟩) (b := ⟨b⟩)
      (c := ⟨c⟩) (Underlying2.hom1 f) (Underlying2.hom1 g))

variable (R) in
include R in
/--
@isnad1 id=eq.0h7v.s8.d11b6e19659b from=translated src=- shape=dc61fa70 vocab=aeabe653
-/
@[reassoc]
theorem whiskerLeft_rightUnitor (f : a ⟶ b) (g : b ⟶ c) :
    f ◁ (rightUnitor g).hom = (associator f g (𝟙 c)).inv ≫ (rightUnitor (f ≫ g)).hom :=
  congrArg Subtype.val
    (Bicategory.whiskerLeft_rightUnitor (B := Underlying2 R B) (a := ⟨a⟩) (b := ⟨b⟩)
      (c := ⟨c⟩) (Underlying2.hom1 f) (Underlying2.hom1 g))

variable (R) in
include R in
/--
@isnad1 id=eq.0h11v.s10.df5c00b08c5c from=translated src=- shape=66bccb46 vocab=353f1058
-/
@[reassoc]
theorem pentagon_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    f ◁ (associator g h i).inv ≫ (associator f (g ≫ h) i).inv ≫ (associator f g h).inv ▷ i =
      (associator f g (h ≫ i)).inv ≫ (associator (f ≫ g) h i).inv :=
  congrArg Subtype.val
    (Bicategory.pentagon_inv (B := Underlying2 R B) (a := ⟨a⟩) (b := ⟨b⟩) (c := ⟨c⟩)
      (d := ⟨d⟩) (e := ⟨e⟩) (Underlying2.hom1 f) (Underlying2.hom1 g) (Underlying2.hom1 h) (Underlying2.hom1 i))

end TwoSupercategory

end StringDiagrams

end
