import Tengoku.DgLean.DG.Category.Functor
import Tengoku.DgLean.DG.Module.Corner

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Corner dg categories of families of idempotents

Let `C` be a dg category and let `eᵢ : Xᵢ ⟶ Xᵢ` (`i : ι`) be a family of degree-`0` cocycle
idempotents of objects of `C` (`DG.IdempotentFamily ι C`). The *corner dg category*
`P.Corner` has objects `ι` and Hom complexes

  `P.Corner(i, j) = eᵢ C(Xᵢ, Xⱼ) eⱼ = {f : Xᵢ ⟶ Xⱼ | eᵢ ≫ f = f ∧ f ≫ eⱼ = f}`,

with the grading and the differential restricted from `C` (both preserve these subgroups since
the `eᵢ` are cocycles of degree `0`), the composition of `C`, and identities `eᵢ`. It is the full
dg subcategory of the (dg) Karoubi envelope of `C` on the objects `(Xᵢ, eᵢ)`.

For a dg ring `A` (`C = SingleObj A`) and a single idempotent `e`, the corner dg category is the
one-object dg category of the corner ring `e A e`.

The family `P.augment` over `C ⊕ ι` consists of the identities `𝟙 X` of all objects of `C`
together with `P`; `C` and `P.Corner` embed into `P.augment.Corner` by the dg functors `P.inl`
and `P.inr`, which are isomorphisms on Hom complexes. This is the setting of Morita theory for
idempotents (`DG.Category.Derived.Morita`).

## Main definitions

* `DG.IdempotentFamily ι C`, `DG.IdempotentFamily.Corner`, with `Category`, `Preadditive`,
  `DGAddCommGroup` (on Hom groups) and `DGCategory` instances.
* `DG.IdempotentFamily.augment` (the family `P` together with all identities `𝟙 X`), and the dg
  functors `DG.IdempotentFamily.inl : C ⥤ P.augment.Corner`,
  `DG.IdempotentFamily.inr : P.Corner ⥤ P.augment.Corner`.
* `DG.IdempotentFamily.mapCorner`, `DG.IdempotentFamily.mapAugment`: the dg endofunctors of
  `P.Corner` and `P.augment.Corner` induced by a dg endofunctor of `C` preserving the family, and
  their compatibility with `P.inl` and `P.inr` (`DG.IdempotentFamily.inlCompMapAugmentIso`,
  `DG.IdempotentFamily.inrCompMapAugmentIso`).
-/

open scoped DG

open CategoryTheory DirectSum

universe w v u

namespace DG

variable (ι : Type w) (C : Type u) [Category.{v} C] [Preadditive C]
  [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]

/-- A family of degree-`0` cocycle idempotents `eᵢ : Xᵢ ⟶ Xᵢ` of objects of a dg category `C`,
indexed by `ι`.-/
structure IdempotentFamily where
  /-- The object carrying the `i`-th idempotent.-/
  obj : ι → C
  /-- The `i`-th idempotent.-/
  idem : ∀ i, obj i ⟶ obj i
  idem_mem : ∀ i, idem i ∈ grading (M := obj i ⟶ obj i) 0
  idem_comp_idem : ∀ i, idem i ≫ idem i = idem i
  d_idem : ∀ i, d (idem i) = 0

namespace IdempotentFamily

variable {ι C} (P : IdempotentFamily ι C)

attribute [reassoc (attr := simp)] idem_comp_idem

/--
@isnad1 id=mem.0h4v.s8.25540c662c56 from=translated src=- shape=02d6f9f3 vocab=0fcca899
-/
theorem idem_mem_cocycles (i : ι) : P.idem i ∈ cocycles (P.obj i ⟶ P.obj i) 0 :=
  ⟨P.idem_mem i, P.d_idem i⟩

/-- The subgroup `eᵢ C(Xᵢ, Xⱼ) eⱼ` of `C(Xᵢ, Xⱼ)`.-/
def homSubgroup (i j : ι) : AddSubgroup (P.obj i ⟶ P.obj j) where
  carrier := {f | P.idem i ≫ f = f ∧ f ≫ P.idem j = f}
  zero_mem' := ⟨Limits.comp_zero, Limits.zero_comp⟩
  add_mem' {f g} hf hg := ⟨by rw [Preadditive.comp_add, hf.1, hg.1],
    by rw [Preadditive.add_comp, hf.2, hg.2]⟩
  neg_mem' {f} hf := ⟨by rw [Preadditive.comp_neg, hf.1], by rw [Preadditive.neg_comp, hf.2]⟩

/--
@isnad1 id=iff.0h6v.s8.00199d5e6b14 from=translated src=- shape=702528ce vocab=5daa13e9
-/
theorem mem_homSubgroup {i j : ι} {f : P.obj i ⟶ P.obj j} :
    f ∈ P.homSubgroup i j ↔ P.idem i ≫ f = f ∧ f ≫ P.idem j = f :=
  Iff.rfl

/--
@isnad1 id=mem.0h6v.s8.6adef8365a99 from=translated src=- shape=fc48c881 vocab=5daa13e9
-/
theorem idem_comp_comp_idem_mem (i j : ι) (f : P.obj i ⟶ P.obj j) :
    P.idem i ≫ f ≫ P.idem j ∈ P.homSubgroup i j :=
  ⟨by simp, by simp⟩

/-- The objects of the corner dg category `P.Corner`: the indices `i : ι`.-/
@[ext]
structure Corner (P : IdempotentFamily ι C) where
  /-- The index underlying an object of the corner dg category.-/
  as : ι

/-- The corner category: `P.Corner(i, j) = eᵢ C(Xᵢ, Xⱼ) eⱼ`, with the composition of `C` and
identities `eᵢ`.-/
instance category : Category.{v} P.Corner where
  Hom i j := P.homSubgroup i.as j.as
  id i := ⟨P.idem i.as, by simp, by simp⟩
  comp f g := ⟨f.1 ≫ g.1, by rw [← Category.assoc, f.2.1], by rw [Category.assoc, g.2.2]⟩
  id_comp f := Subtype.ext f.2.1
  comp_id f := Subtype.ext f.2.2
  assoc f g h := Subtype.ext (Category.assoc f.1 g.1 h.1)

variable {P}

/--
@isnad1 id=eq.1h7v.s10.20ab0c0bd6da from=translated src=- shape=cf2837b1 vocab=f6f400e7
-/
theorem hom_ext {i j : P.Corner} {f g : i ⟶ j} (h : f.1 = g.1) : f = g :=
  Subtype.ext h

/--
@isnad1 id=eq.0h4v.s9.4354cdf06493 from=translated src=- shape=c49f593d vocab=d4a7a861
-/
@[simp] theorem id_val (i : P.Corner) : (𝟙 i : i ⟶ i).1 = P.idem i.as := rfl

/--
@isnad1 id=eq.0h8v.s10.8e44f96dcdfe from=translated src=- shape=c10923ea vocab=5a13b178
-/
@[simp] theorem comp_val {i j k : P.Corner} (f : i ⟶ j) (g : j ⟶ k) :
    (f ≫ g).1 = f.1 ≫ g.1 := rfl

/--
@isnad1 id=eq.0h6v.s10.d167cb44ab46 from=translated src=- shape=1e1128c8 vocab=e385524e
-/
theorem idem_comp_val {i j : P.Corner} (f : i ⟶ j) : P.idem i.as ≫ f.1 = f.1 := f.2.1

/--
@isnad1 id=eq.0h6v.s10.dd0715647a2d from=translated src=- shape=18a1e9ec vocab=e385524e
-/
theorem val_comp_idem {i j : P.Corner} (f : i ⟶ j) : f.1 ≫ P.idem j.as = f.1 := f.2.2

instance (i j : P.Corner) : AddCommGroup (i ⟶ j) :=
  inferInstanceAs (AddCommGroup (P.homSubgroup i.as j.as))

/--
@isnad1 id=eq.0h7v.s11.e9f4f7599c9b from=translated src=- shape=e63c3dbf vocab=2879f18f
-/
@[simp] theorem add_val {i j : P.Corner} (f g : i ⟶ j) : (f + g).1 = f.1 + g.1 := rfl
/--
@isnad1 id=eq.0h6v.s10.1469be0913ba from=translated src=- shape=7ae59695 vocab=609e02bf
-/
@[simp] theorem neg_val {i j : P.Corner} (f : i ⟶ j) : (-f).1 = -f.1 := rfl
/--
@isnad1 id=eq.0h5v.s9.8d13fdebfd57 from=translated src=- shape=b404a8c5 vocab=f6f400e7
-/
@[simp] theorem zero_val (i j : P.Corner) : (0 : i ⟶ j).1 = 0 := rfl
/--
@isnad1 id=eq.0h7v.s11.111ce1b038a5 from=translated src=- shape=e63c3dbf vocab=1700308b
-/
@[simp] theorem sub_val {i j : P.Corner} (f g : i ⟶ j) : (f - g).1 = f.1 - g.1 := rfl
/--
@isnad1 id=eq.0h7v.s10.4491defbdf9b from=translated src=- shape=6f0bb219 vocab=7b22392a
-/
@[simp] theorem zsmul_val {i j : P.Corner} (n : ℤ) (f : i ⟶ j) : (n • f).1 = n • f.1 := rfl

/--
@isnad1 id=eq.0h8v.s10.b633e0560dac from=translated src=- shape=f5f82952 vocab=b241e422
-/
@[simp] theorem sum_val {i j : P.Corner} {J : Type*} (s : Finset J) (f : J → (i ⟶ j)) :
    (∑ a ∈ s, f a).1 = ∑ a ∈ s, (f a).1 :=
  map_sum (AddSubgroupClass.subtype (P.homSubgroup i.as j.as)) f s

instance preadditive : Preadditive P.Corner where
  add_comp _ _ _ f f' g := hom_ext (by simp only [comp_val, add_val, Preadditive.add_comp])
  comp_add _ _ _ f g g' := hom_ext (by simp only [comp_val, add_val, Preadditive.comp_add])

variable [DGCategory C]

variable (P) in
/--
@isnad1 id=mem.1h6v.s10.f92991aac72d from=translated src=- shape=bc7148cd vocab=264bacae
-/
theorem d_mem_homSubgroup {i j : ι} {f : P.obj i ⟶ P.obj j} (hf : f ∈ P.homSubgroup i j) :
    d f ∈ P.homSubgroup i j := by
  constructor
  · rw [← d_comp_of_d_eq_zero_left (P.d_idem i), hf.1]
  · have h := d_comp_of_mem_zero f (P.idem_mem j)
    rw [P.d_idem, Limits.comp_zero, zero_add, hf.2] at h
    exact h.symm

variable (P) in
/--
@isnad1 id=mem.1h7v.s13.58f48a1a4724 from=translated src=- shape=eea8d555 vocab=0f47c4d6
-/
theorem decompose_mem_homSubgroup {i j : ι} {f : P.obj i ⟶ P.obj j}
    (hf : f ∈ P.homSubgroup i j) (n : ℤ) :
    (decompose (grading (M := P.obj i ⟶ P.obj j)) f n : P.obj i ⟶ P.obj j) ∈
      P.homSubgroup i j := by
  constructor
  · have h := decompose_comp_left (P.idem_mem i) f n
    rw [add_zero, hf.1] at h
    exact h.symm
  · have h := decompose_comp_right f (P.idem_mem j) n
    rw [add_zero, hf.2] at h
    exact h.symm

/-- The Hom complexes of the corner category: the subcomplexes `eᵢ C(Xᵢ, Xⱼ) eⱼ`.-/
noncomputable instance instDGAddCommGroupHom (i j : P.Corner) : DGAddCommGroup (i ⟶ j) :=
  DGAddCommGroup.ofInjective (AddSubgroupClass.subtype (P.homSubgroup i.as j.as))
    Subtype.val_injective
    (((d : (P.obj i.as ⟶ P.obj j.as) →+ _).comp (AddSubgroupClass.subtype _)).codRestrict _
      fun f => P.d_mem_homSubgroup f.2)
    (fun _ => rfl) fun n f => ⟨⟨_, P.decompose_mem_homSubgroup f.2 n⟩, rfl⟩

/--
@isnad1 id=iff.0h7v.s10.50adb8e6aa5e from=translated src=- shape=a53ec3ad vocab=c451eda3
-/
theorem mem_grading_iff {i j : P.Corner} {n : ℤ} {f : i ⟶ j} :
    f ∈ grading n ↔ f.1 ∈ grading (M := P.obj i.as ⟶ P.obj j.as) n :=
  Iff.rfl

/--
@isnad1 id=eq.0h6v.s11.6e6bafcbf737 from=translated src=- shape=a8c010db vocab=6132ffc1
-/
@[simp]
theorem d_val {i j : P.Corner} (f : i ⟶ j) : (d f).1 = d f.1 := rfl

/--
@isnad1 id=iff.0h7v.s10.f3c4489cab16 from=translated src=- shape=e376f465 vocab=08c43f4c
-/
theorem mem_cocycles_iff {i j : P.Corner} {n : ℤ} {f : i ⟶ j} :
    f ∈ cocycles (i ⟶ j) n ↔ f.1 ∈ cocycles (P.obj i.as ⟶ P.obj j.as) n := by
  simp only [mem_cocycles, mem_grading_iff]
  exact and_congr_right fun _ => ⟨fun h => by rw [← d_val, h, zero_val],
    fun h => hom_ext (by rw [d_val, h, zero_val])⟩

/-- The corner category of a family of degree-`0` cocycle idempotents is a dg category.
@isnad1 id=dgcatego.0h3v.s6.f4ea1b14cf0c from=translated src=- shape=b76e3636 vocab=a547b5f8
-/
instance instDGCategory : DGCategory P.Corner where
  comp_mem' hf hg := comp_mem_grading (C := C) hf hg
  id_mem' i := P.idem_mem i.as
  d_comp' f _ hg := hom_ext (d_comp (C := C) f.1 hg)

/-! ### The augmented family and the embeddings of `C` and of `P.Corner` -/

section Augment

variable (P)

/-- The family over `C ⊕ ι` consisting of the identities `𝟙 X` of all objects of `C` together with
the family `P`.-/
def augment : IdempotentFamily (C ⊕ ι) C where
  obj := Sum.elim id P.obj
  idem
    | .inl X => 𝟙 X
    | .inr i => P.idem i
  idem_mem
    | .inl X => id_mem_grading X
    | .inr i => P.idem_mem i
  idem_comp_idem
    | .inl _ => Category.id_comp _
    | .inr i => P.idem_comp_idem i
  d_idem
    | .inl X => d_id X
    | .inr i => P.d_idem i

/--
@isnad1 id=eq.0h4v.s6.da1d8ce6131f from=translated src=- shape=b178f0b4 vocab=2e0987e0
-/
@[simp] theorem augment_obj_inl (X : C) : P.augment.obj (.inl X) = X := rfl
/--
@isnad1 id=eq.0h4v.s6.56894e67959e from=translated src=- shape=48f010bc vocab=659a356c
-/
@[simp] theorem augment_obj_inr (i : ι) : P.augment.obj (.inr i) = P.obj i := rfl
/--
@isnad1 id=eq.0h4v.s6.de3a4d7cf59f from=translated src=- shape=df9db7a9 vocab=3c46631d
-/
@[simp] theorem augment_idem_inl (X : C) : P.augment.idem (.inl X) = 𝟙 X := rfl
/--
@isnad1 id=eq.0h4v.s6.f6bda609b785 from=translated src=- shape=be3fdb81 vocab=e3af3dc2
-/
@[simp] theorem augment_idem_inr (i : ι) : P.augment.idem (.inr i) = P.idem i := rfl

/-- The dg functor `C ⥤ P.augment.Corner`, `X ↦ (X, 𝟙 X)`, the identity on Hom complexes.-/
@[simps obj]
def inl : C ⥤ P.augment.Corner where
  obj X := ⟨.inl X⟩
  map f := ⟨f, Category.id_comp f, Category.comp_id f⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/--
@isnad1 id=eq.0h6v.s11.643597175338 from=translated src=- shape=143a695d vocab=65fcd8b0
-/
@[simp] theorem inl_map_val {X Y : C} (f : X ⟶ Y) : ((P.inl).map f).1 = f := rfl

/-- The dg functor `P.Corner ⥤ P.augment.Corner`, `i ↦ (Xᵢ, eᵢ)`, the identity on Hom
complexes.-/
@[simps obj]
def inr : P.Corner ⥤ P.augment.Corner where
  obj i := ⟨.inr i.as⟩
  map f := ⟨f.1, f.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/--
@isnad1 id=eq.0h6v.s11.926c0e4c46f4 from=translated src=- shape=68885a91 vocab=ef4bf95d
-/
@[simp] theorem inr_map_val {i j : P.Corner} (f : i ⟶ j) : ((P.inr).map f).1 = f.1 := rfl

instance : P.inl.Additive where
instance : P.inr.Additive where

instance : P.inl.IsDGFunctor where
  map_mem' hf := hf
  map_d' _ := rfl

instance : P.inr.IsDGFunctor where
  map_mem' hf := hf
  map_d' _ := rfl

end Augment

/-! ### Dg endofunctors preserving the family -/

section Map

variable {X Y Z : C}

/--
@isnad1 id=mem.1h3v.s7.7573c7df3c73 from=translated src=- shape=4e2854f1 vocab=bba2e348
-/
theorem eqToHom_mem_cocycles (h : X = Y) : eqToHom h ∈ cocycles (X ⟶ Y) 0 := by
  subst h
  exact id_mem_cocycles X

omit [DGCategory C] in
/--
@isnad1 id=mem.3h7v.s8.b427996fa032 from=translated src=- shape=5ecb09e7 vocab=eb59a6b8
-/
theorem eqToHom_comp_comp_eqToHom_mem {X' Y' : C} (h : X' = X) (h' : Y = Y') {n : ℤ}
    {f : X ⟶ Y} (hf : f ∈ grading n) : eqToHom h ≫ f ≫ eqToHom h' ∈ grading n := by
  subst h h'
  simpa using hf

omit [DGCategory C] in
/--
@isnad1 id=eq.2h6v.s9.c97f28f3678a from=translated src=- shape=3facb7e6 vocab=00fecd78
-/
theorem d_eqToHom_comp_comp_eqToHom {X' Y' : C} (h : X' = X) (h' : Y = Y') (f : X ⟶ Y) :
    d (eqToHom h ≫ f ≫ eqToHom h') = eqToHom h ≫ d f ≫ eqToHom h' := by
  subst h h'
  simp

variable (P) (σ : C ⥤ C) [σ.Additive] [σ.IsDGFunctor] (τ : ι → ι)
  (hobj : ∀ i, σ.obj (P.obj i) = P.obj (τ i))
  (hidem : ∀ i, eqToHom (hobj i).symm ≫ σ.map (P.idem i) ≫ eqToHom (hobj i) = P.idem (τ i))

/-- A dg endofunctor `σ` of `C` carrying the family `P` to itself along `τ : ι → ι`
(`σ Xᵢ = X_{τ i}` and `σ eᵢ = e_{τ i}`) induces the dg endofunctor `i ↦ τ i` of `P.Corner`,
`f ↦ σ f`.-/
@[simps obj]
def mapCorner : P.Corner ⥤ P.Corner where
  obj i := ⟨τ i.as⟩
  map {i j} f := ⟨eqToHom (hobj i.as).symm ≫ σ.map f.1 ≫ eqToHom (hobj j.as), by
    rw [← hidem]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      ← Functor.map_comp_assoc, idem_comp_val], by
    rw [← hidem]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      ← Functor.map_comp_assoc, val_comp_idem]⟩
  map_id i := hom_ext (hidem i.as)
  map_comp f g := hom_ext (by simp)

omit [DGCategory C] [σ.Additive] [σ.IsDGFunctor] in
/--
@isnad1 id=eq.2h8v.s11.ac63c582450a from=translated src=- shape=9b3dc6e7 vocab=2d05602b
-/
@[simp]
theorem mapCorner_map_val {i j : P.Corner} (f : i ⟶ j) :
    ((P.mapCorner σ τ hobj hidem).map f).1 =
      eqToHom (hobj i.as).symm ≫ σ.map f.1 ≫ eqToHom (hobj j.as) :=
  rfl

instance : (P.mapCorner σ τ hobj hidem).Additive where
  map_add {_ _ f g} := hom_ext (by
    rw [mapCorner_map_val, add_val, σ.map_add, Preadditive.add_comp, Preadditive.comp_add]
    rfl)

instance : (P.mapCorner σ τ hobj hidem).IsDGFunctor where
  map_mem' hf := eqToHom_comp_comp_eqToHom_mem _ _ (σ.map_mem_grading hf)
  map_d' f := hom_ext (by
    change eqToHom _ ≫ σ.map (d f.1) ≫ eqToHom _ = d (eqToHom _ ≫ σ.map f.1 ≫ eqToHom _)
    rw [d_eqToHom_comp_comp_eqToHom, σ.map_d])

omit [σ.Additive] [σ.IsDGFunctor] in
include hobj in
/--
@isnad1 id=eq.1h6v.s7.38d0a8ef100c from=translated src=- shape=2abc864a vocab=c026d8cc
-/
theorem augment_hobj : ∀ x, σ.obj (P.augment.obj x) = P.augment.obj (Sum.map σ.obj τ x)
  | .inl _ => rfl
  | .inr i => hobj i

omit [σ.Additive] [σ.IsDGFunctor] in
include hidem in
/--
@isnad1 id=eq.2h6v.s9.56f1f71cb685 from=translated src=- shape=8b87638e vocab=53eddef0
-/
theorem augment_hidem : ∀ x, eqToHom (P.augment_hobj σ τ hobj x).symm ≫
    σ.map (P.augment.idem x) ≫ eqToHom (P.augment_hobj σ τ hobj x) =
      P.augment.idem (Sum.map σ.obj τ x)
  | .inl X => by
    change eqToHom _ ≫ σ.map (𝟙 X) ≫ eqToHom _ = 𝟙 (σ.obj X)
    erw [eqToHom_refl]
    simp
  | .inr i => hidem i

/-- The dg endofunctor of `P.augment.Corner` induced by `σ`: `(X, 𝟙) ↦ (σ X, 𝟙)` and
`(Xᵢ, eᵢ) ↦ (X_{τ i}, e_{τ i})`.-/
abbrev mapAugment : P.augment.Corner ⥤ P.augment.Corner :=
  P.augment.mapCorner σ (Sum.map σ.obj τ) (P.augment_hobj σ τ hobj)
    (P.augment_hidem σ τ hobj hidem)

/-- `P.inl` commutes with `σ`.-/
def inlCompMapAugmentIso : P.inl ⋙ P.mapAugment σ τ hobj hidem ≅ σ ⋙ P.inl :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun {X Y} f => hom_ext (by
    change (eqToHom _ ≫ σ.map f ≫ eqToHom _) ≫ 𝟙 (σ.obj Y) = 𝟙 (σ.obj X) ≫ σ.map f
    erw [eqToHom_refl, eqToHom_refl]
    simp)

/-- `P.inr` commutes with `σ`.-/
def inrCompMapAugmentIso :
    P.inr ⋙ P.mapAugment σ τ hobj hidem ≅ P.mapCorner σ τ hobj hidem ⋙ P.inr :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun {i j} f => hom_ext (by
    change (eqToHom (hobj i.as).symm ≫ σ.map f.1 ≫ eqToHom (hobj j.as)) ≫ P.idem (τ j.as) =
      P.idem (τ i.as) ≫ (eqToHom (hobj i.as).symm ≫ σ.map f.1 ≫ eqToHom (hobj j.as))
    rw [← hidem, ← hidem]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      ← Functor.map_comp_assoc, idem_comp_val, val_comp_idem])

end Map

end IdempotentFamily

end DG
