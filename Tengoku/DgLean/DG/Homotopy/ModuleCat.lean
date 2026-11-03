import Tengoku.Seed.CategoryTheory.Linear.Basic
import Tengoku.Seed.CategoryTheory.Preadditive.Biproducts
import Tengoku.Seed.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Tengoku.Seed.CategoryTheory.ConcreteCategory.Basic
import Tengoku.Seed.CategoryTheory.ConcreteCategory.Forget
import Tengoku.DgLean.DG.Algebra.Decompose
import Tengoku.DgLean.DG.Module.PUnit
import Tengoku.DgLean.DG.Module.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The category of dg modules

`DG.DGModuleCat.{v} A` is the category of bundled dg `A`-modules with carrier in `Type v`, for a
dg ring `A`. It is built in the style of Mathlib's `ModuleCat`: objects are structures carrying
a type with its instances, and morphisms are a one-field structure wrapping
`DG.DGModuleHom A M N` (`M →ᵈᵍ[A] N`), so that `DGModuleCat A` is a concrete category.

The category is preadditive (morphisms form abelian groups under pointwise addition), has a zero
object (the zero module), and has finite biproducts (`M × N` with its componentwise dg
structure, `DG.Prod.instDGAddCommGroup`).

For a dg `R`-algebra `A`, the category is `R`-linear: `R` acts on `M →ᵈᵍ[A] N` through the
structure map, `(r • f) m = algebraMap R A r • f m` (`DG.DGModuleHom.instModule`). This action
is `A`-linear because `algebraMap R A r` is central in `A`, and commutes with `d` because the
image of `R` is killed by `d` and sits in degree `0`.

## Implementation notes

The `R`-module structure on `M →ᵈᵍ[A] N` and the `Linear R` instance are declared with a low
priority: for `R = ℤ` they agree with the integer action of the abelian group structure only
propositionally, and Mathlib's `AddCommGroup.toIntModule` and `Linear.preadditiveIntLinear`
should be found first.
-/

open scoped DG

open CategoryTheory CategoryTheory.Limits

universe v u

namespace DG

variable (A : Type u) [Ring A] [DGAddCommGroup A]

/-- The category of dg `A`-modules with carriers in `Type v`.-/
structure DGModuleCat where
  /-- The underlying type of a dg module.-/
  carrier : Type v
  [isAddCommGroup : AddCommGroup carrier]
  [isDGAddCommGroup : DGAddCommGroup carrier]
  [isModule : Module A carrier]
  [isDGModule : DGModule A carrier]

attribute [instance] DGModuleCat.isAddCommGroup DGModuleCat.isDGAddCommGroup
  DGModuleCat.isModule DGModuleCat.isDGModule

namespace DGModuleCat

instance : CoeSort (DGModuleCat.{v} A) (Type v) :=
  ⟨DGModuleCat.carrier⟩

attribute [coe] DGModuleCat.carrier

/-- The object of `DGModuleCat A` associated to a type with a dg `A`-module structure.-/
abbrev of (M : Type v) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M] :
    DGModuleCat.{v} A :=
  ⟨M⟩

/--
@isnad1 id=eq.0h2v.s5.01d41bfd0bd8 from=translated src=- shape=f88b447e vocab=fa0abb9b
-/
theorem coe_of (M : Type v) [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M] :
    (of A M : Type v) = M :=
  rfl

variable {A}

/-- The type of morphisms in `DGModuleCat A`.-/
@[ext]
structure Hom (M N : DGModuleCat.{v} A) where
  /-- The underlying morphism of dg modules.-/
  hom' : M →ᵈᵍ[A] N

instance category : Category.{v, max (v + 1) u} (DGModuleCat.{v} A) where
  Hom M N := Hom M N
  id _ := ⟨DGModuleHom.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance concreteCategory : ConcreteCategory (DGModuleCat.{v} A) (· →ᵈᵍ[A] ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- The morphism of dg modules underlying a morphism in `DGModuleCat A`.-/
abbrev Hom.hom {M N : DGModuleCat.{v} A} (f : Hom M N) : M →ᵈᵍ[A] N :=
  ConcreteCategory.hom (C := DGModuleCat A) f

/-- A morphism of dg modules as a morphism in `DGModuleCat A`.-/
abbrev ofHom {M N : Type v} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
    [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N] (f : M →ᵈᵍ[A] N) :
    of A M ⟶ of A N :=
  ConcreteCategory.ofHom (C := DGModuleCat A) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.-/
def Hom.Simps.hom (M N : DGModuleCat.{v} A) (f : Hom M N) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/--
@isnad1 id=eq.0h2v.s6.27fbfa621dd9 from=translated src=- shape=e594d77a vocab=d616405e
-/
@[simp]
theorem hom_id {M : DGModuleCat.{v} A} : (𝟙 M : M ⟶ M).hom = DGModuleHom.id := rfl

/--
@isnad1 id=eq.0h3v.s8.0e060d19c2ac from=translated src=- shape=a1da1b31 vocab=fbe22910
-/
theorem id_apply (M : DGModuleCat.{v} A) (x : M) : (𝟙 M : M ⟶ M) x = x := rfl

/--
@isnad1 id=eq.0h6v.s7.a6e0d0203c0b from=translated src=- shape=b6ebf4b6 vocab=269f4986
-/
@[simp]
theorem hom_comp {M N P : DGModuleCat.{v} A} (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/--
@isnad1 id=eq.0h7v.s9.99f5e9c10978 from=translated src=- shape=ca3aba3b vocab=1fe0a2ce
-/
theorem comp_apply {M N P : DGModuleCat.{v} A} (f : M ⟶ N) (g : N ⟶ P) (x : M) :
    (f ≫ g) x = g (f x) := rfl

/--
@isnad1 id=eq.1h5v.s7.89e4ca8c2b34 from=translated src=- shape=f4103be7 vocab=f7872b93
-/
@[ext]
theorem hom_ext {M N : DGModuleCat.{v} A} {f g : M ⟶ N} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

/--
@isnad1 id=eq.1h5v.s9.29223462c881 from=translated src=- shape=ca18e0cc vocab=eb680cf2
-/
theorem hom_ext_apply {M N : DGModuleCat.{v} A} {f g : M ⟶ N} (h : ∀ x, f x = g x) : f = g :=
  hom_ext (DGModuleHom.ext h)

/--
@isnad1 id=bijectiv.0h3v.s6.38cb27784eb3 from=translated src=- shape=b5350857 vocab=2682ca05
-/
theorem hom_bijective {M N : DGModuleCat.{v} A} :
    Function.Bijective (Hom.hom : (M ⟶ N) → (M →ᵈᵍ[A] N)) where
  left f g h := by cases f; cases g; exact congrArg _ h
  right f := ⟨⟨f⟩, rfl⟩

/--
@isnad1 id=injectiv.0h3v.s6.441b03d7f9c4 from=translated src=- shape=b5350857 vocab=a91e9711
-/
theorem hom_injective {M N : DGModuleCat.{v} A} :
    Function.Injective (Hom.hom : (M ⟶ N) → (M →ᵈᵍ[A] N)) :=
  hom_bijective.injective

/--
@isnad1 id=surjecti.0h3v.s6.e752ad387bd4 from=translated src=- shape=b5350857 vocab=f908e5c1
-/
theorem hom_surjective {M N : DGModuleCat.{v} A} :
    Function.Surjective (Hom.hom : (M ⟶ N) → (M →ᵈᵍ[A] N)) :=
  hom_bijective.surjective

/--
@isnad1 id=eq.0h4v.s7.7c8f100adb0c from=translated src=- shape=402e67a2 vocab=4b2821d0
-/
@[simp]
theorem hom_ofHom {M N : Type v} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
    [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N] (f : M →ᵈᵍ[A] N) :
    (ofHom f).hom = f := rfl

/--
@isnad1 id=eq.0h4v.s7.5588cdc668ae from=translated src=- shape=434ec837 vocab=1d86f0e3
-/
@[simp]
theorem ofHom_hom {M N : DGModuleCat.{v} A} (f : M ⟶ N) : ofHom f.hom = f := rfl

/--
@isnad1 id=eq.0h2v.s6.fdd64f6cb639 from=translated src=- shape=4980b416 vocab=70cd16eb
-/
@[simp]
theorem ofHom_id {M : Type v} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M] :
    ofHom (DGModuleHom.id : M →ᵈᵍ[A] M) = 𝟙 (of A M) := rfl

/--
@isnad1 id=eq.0h6v.s8.ad068910e262 from=translated src=- shape=efcb25a7 vocab=2e078eb7
-/
@[simp]
theorem ofHom_comp {M N P : Type v} [AddCommGroup M] [DGAddCommGroup M] [Module A M]
    [DGModule A M] [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N]
    [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]
    (f : M →ᵈᵍ[A] N) (g : N →ᵈᵍ[A] P) : ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

/--
@isnad1 id=eq.0h5v.s8.14921221455b from=translated src=- shape=38e01024 vocab=887f97a0
-/
theorem ofHom_apply {M N : Type v} [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
    [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N] (f : M →ᵈᵍ[A] N) (x : M) :
    ofHom f x = f x := rfl

/-- `DGModuleCat.Hom.hom` bundled as an equivalence.-/
def homEquiv {M N : DGModuleCat.{v} A} : (M ⟶ N) ≃ (M →ᵈᵍ[A] N) where
  toFun := Hom.hom
  invFun := ofHom
  left_inv _ := rfl
  right_inv _ := rfl

instance : Inhabited (DGModuleCat.{v} A) :=
  ⟨of A PUnit⟩

/-! ### Preadditive structure -/

section AddCommGroup

variable {M N : DGModuleCat.{v} A}

instance : Add (M ⟶ N) where
  add f g := ⟨f.hom + g.hom⟩

/--
@isnad1 id=eq.0h5v.s8.7b14b1c7776e from=translated src=- shape=0830244e vocab=3bbf8818
-/
@[simp] theorem hom_add (f g : M ⟶ N) : (f + g).hom = f.hom + g.hom := rfl

instance : Zero (M ⟶ N) where
  zero := ⟨0⟩

/--
@isnad1 id=eq.0h3v.s8.126640f8a44a from=translated src=- shape=a6de38d0 vocab=f7872b93
-/
@[simp] theorem hom_zero : (0 : M ⟶ N).hom = 0 := rfl

instance : SMul ℕ (M ⟶ N) where
  smul n f := ⟨n • f.hom⟩

/--
@isnad1 id=eq.0h5v.s8.7aa66f718871 from=translated src=- shape=7eaf3948 vocab=76e75218
-/
@[simp] theorem hom_nsmul (n : ℕ) (f : M ⟶ N) : (n • f).hom = n • f.hom := rfl

instance : Neg (M ⟶ N) where
  neg f := ⟨-f.hom⟩

/--
@isnad1 id=eq.0h4v.s7.0ec1933c9a63 from=translated src=- shape=43f6de25 vocab=7df61b8c
-/
@[simp] theorem hom_neg (f : M ⟶ N) : (-f).hom = -f.hom := rfl

instance : Sub (M ⟶ N) where
  sub f g := ⟨f.hom - g.hom⟩

/--
@isnad1 id=eq.0h5v.s8.05ee77b09563 from=translated src=- shape=0830244e vocab=188c327d
-/
@[simp] theorem hom_sub (f g : M ⟶ N) : (f - g).hom = f.hom - g.hom := rfl

instance : SMul ℤ (M ⟶ N) where
  smul n f := ⟨n • f.hom⟩

/--
@isnad1 id=eq.0h5v.s8.e283c082e8ae from=translated src=- shape=7eaf3948 vocab=4f033baa
-/
@[simp] theorem hom_zsmul (n : ℤ) (f : M ⟶ N) : (n • f).hom = n • f.hom := rfl

instance : AddCommGroup (M ⟶ N) :=
  Function.Injective.addCommGroup (Hom.hom) hom_injective
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/--
@isnad1 id=eq.0h6v.s9.7c9fb17ee3c6 from=translated src=- shape=a12ea769 vocab=1b84a2b5
-/
@[simp] theorem add_apply (f g : M ⟶ N) (x : M) : (f + g) x = f x + g x := rfl
/--
@isnad1 id=eq.0h4v.s8.ef6603f83e0c from=translated src=- shape=3258605a vocab=eb680cf2
-/
@[simp] theorem zero_apply (x : M) : (0 : M ⟶ N) x = 0 := rfl
/--
@isnad1 id=eq.0h5v.s9.fd8efb3c30b4 from=translated src=- shape=e495887a vocab=c0f3beb8
-/
@[simp] theorem neg_apply (f : M ⟶ N) (x : M) : (-f) x = -f x := rfl
/--
@isnad1 id=eq.0h6v.s9.581613e9c692 from=translated src=- shape=a12ea769 vocab=366286d0
-/
@[simp] theorem sub_apply (f g : M ⟶ N) (x : M) : (f - g) x = f x - g x := rfl

instance preadditive : Preadditive (DGModuleCat.{v} A) where
  add_comp _ _ _ _ _ _ := hom_ext_apply fun _ => by simp only [comp_apply, add_apply, map_add]
  comp_add _ _ _ _ _ _ := hom_ext_apply fun _ => by simp only [comp_apply, add_apply]

/-- `DGModuleCat.Hom.hom` bundled as an additive equivalence.-/
@[simps!]
def homAddEquiv : (M ⟶ N) ≃+ (M →ᵈᵍ[A] N) :=
  { homEquiv with map_add' := fun _ _ => rfl }

end AddCommGroup

/-! ### The zero object -/

/--
@isnad1 id=iszero.0h2v.s5.98f890c635da from=translated src=- shape=9b4d5027 vocab=9655e5fb
-/
theorem isZero_of_subsingleton (M : DGModuleCat.{v} A) [Subsingleton M] : IsZero M where
  unique_to N := ⟨⟨⟨0⟩, fun f => hom_ext_apply fun x => by
    rw [Subsingleton.elim x 0, map_zero, map_zero]⟩⟩
  unique_from N := ⟨⟨⟨0⟩, fun _ => hom_ext_apply fun _ => Subsingleton.elim _ _⟩⟩

/--
@isnad1 id=haszeroo.0h1v.s4.4758be4bb682 from=translated src=- shape=9499e9bc vocab=9af12dc9
-/
instance hasZeroObject : HasZeroObject (DGModuleCat.{v} A) :=
  ⟨⟨of A PUnit, isZero_of_subsingleton _⟩⟩

/-! ### Finite biproducts -/

section Biproducts

variable (M N : DGModuleCat.{v} A)

/-- The binary product of two dg modules, computed on `M × N`.-/
def binaryProductLimitCone : LimitCone (pair M N) where
  cone := BinaryFan.mk (P := of A (M × N)) (ofHom (DGModuleHom.fst M N))
    (ofHom (DGModuleHom.snd M N))
  isLimit := BinaryFan.isLimitMk (fun s => ofHom (DGModuleHom.prod M N s.fst.hom s.snd.hom))
    (fun _ => rfl) (fun _ => rfl) fun s _ h₁ h₂ => hom_ext_apply fun x =>
      Prod.ext (congrArg (fun φ : s.pt ⟶ M => φ x) h₁) (congrArg (fun φ : s.pt ⟶ N => φ x) h₂)

instance : HasLimit (pair M N) :=
  HasLimit.mk (binaryProductLimitCone M N)

/--
@isnad1 id=hasbinar.0h1v.s4.d53cf8914c1f from=translated src=- shape=9499e9bc vocab=58dbea0c
-/
instance hasBinaryProducts : HasBinaryProducts (DGModuleCat.{v} A) :=
  hasBinaryProducts_of_hasLimit_pair _

/--
@isnad1 id=hasfinit.0h1v.s4.2ed17c4d5343 from=translated src=- shape=9499e9bc vocab=55f80ca0
-/
instance hasFiniteProducts : HasFiniteProducts (DGModuleCat.{v} A) :=
  hasFiniteProducts_of_has_binary_and_terminal

/--
@isnad1 id=hasbinar.0h1v.s5.cc2eae11c25b from=translated src=- shape=9499e9bc vocab=d9269aaa
-/
instance hasBinaryBiproducts : HasBinaryBiproducts (DGModuleCat.{v} A) :=
  HasBinaryBiproducts.of_hasBinaryProducts

/--
@isnad1 id=hasfinit.0h1v.s5.8170c6aac248 from=translated src=- shape=9499e9bc vocab=97991b2f
-/
instance hasFiniteBiproducts : HasFiniteBiproducts (DGModuleCat.{v} A) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The biproduct in `DGModuleCat A` is the product `M × N` with its dg structure.-/
noncomputable def biprodIsoProd : (M ⊞ N : DGModuleCat.{v} A) ≅ of A (M × N) :=
  IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit M N) (binaryProductLimitCone M N).isLimit

/--
@isnad1 id=eq.0h3v.s9.129e80059cda from=translated src=- shape=76f8ad99 vocab=09d7e666
-/
@[simp]
theorem biprodIsoProd_inv_comp_fst :
    (biprodIsoProd M N).inv ≫ biprod.fst = ofHom (DGModuleHom.fst M N) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.left)

/--
@isnad1 id=eq.0h3v.s9.f89e1ae6fcc7 from=translated src=- shape=42543e6d vocab=54e788ef
-/
@[simp]
theorem biprodIsoProd_inv_comp_snd :
    (biprodIsoProd M N).inv ≫ biprod.snd = ofHom (DGModuleHom.snd M N) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.right)

end Biproducts

end DGModuleCat

/-! ### Isomorphisms -/

namespace DGModuleHom

variable {A} {M N : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N]

/-- The inverse of a bijective morphism of dg modules is a morphism of dg modules.-/
noncomputable def inverse (f : M →ᵈᵍ[A] N) (hf : Function.Bijective f) : N →ᵈᵍ[A] M where
  __ := (LinearEquiv.ofBijective f.toLinearMap hf).symm
  map_mem' := by
    intro n x hx
    refine mem_grading_of_injective f.toLinearMap.toAddMonoidHom (fun h => f.map_mem h)
      hf.injective ?_
    have h := (LinearEquiv.ofBijective f.toLinearMap hf).apply_symm_apply x
    rw [LinearEquiv.ofBijective_apply] at h
    change f ((LinearEquiv.ofBijective f.toLinearMap hf).symm x) ∈ _
    rwa [← toLinearMap_apply, h]
  map_d' x := by
    apply hf.injective
    have h := fun y => (LinearEquiv.ofBijective f.toLinearMap hf).apply_symm_apply y
    simp only [LinearEquiv.ofBijective_apply] at h
    change f ((LinearEquiv.ofBijective f.toLinearMap hf).symm (d x)) =
      f (d ((LinearEquiv.ofBijective f.toLinearMap hf).symm x))
    rw [map_d, ← toLinearMap_apply, ← toLinearMap_apply, h, h]

/--
@isnad1 id=eq.1h5v.s7.036fdc319470 from=translated src=- shape=2f4dfdc2 vocab=70b3b166
-/
@[simp]
theorem apply_inverse_apply (f : M →ᵈᵍ[A] N) (hf : Function.Bijective f) (x : N) :
    f (f.inverse hf x) = x :=
  (LinearEquiv.ofBijective f.toLinearMap hf).apply_symm_apply x

/--
@isnad1 id=eq.1h5v.s7.0e29e2b1bd70 from=translated src=- shape=d91093de vocab=70b3b166
-/
@[simp]
theorem inverse_apply_apply (f : M →ᵈᵍ[A] N) (hf : Function.Bijective f) (x : M) :
    f.inverse hf (f x) = x :=
  hf.injective (apply_inverse_apply f hf (f x))

end DGModuleHom

namespace DGModuleCat

variable {A}

/-- A bijective morphism in `DGModuleCat A` is an isomorphism.
@isnad1 id=isiso.1h4v.s8.bf72749efe78 from=translated src=- shape=3553debe vocab=e1c421f3
-/
theorem isIso_of_bijective {M N : DGModuleCat.{v} A} (f : M ⟶ N) (hf : Function.Bijective f) :
    IsIso f :=
  ⟨⟨ofHom (f.hom.inverse hf), hom_ext_apply fun x => DGModuleHom.inverse_apply_apply f.hom hf x,
    hom_ext_apply fun x => DGModuleHom.apply_inverse_apply f.hom hf x⟩⟩

end DGModuleCat

/-! ### `R`-linearity -/

namespace DGModuleHom

variable {A} {R : Type*} [CommRing R] [Algebra R A] [DGRing A] [DGAlgebra R A]
  {M N P : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N]
  [AddCommGroup P] [DGAddCommGroup P] [Module A P] [DGModule A P]

/-- The action of `R` on `M →ᵈᵍ[A] N` for a dg `R`-algebra `A`:
`(r • f) m = algebraMap R A r • f m`.
See the implementation notes of `DG.Homotopy.ModuleCat` for the priority.-/
instance (priority := 100) instSMul : SMul R (M →ᵈᵍ[A] N) :=
  ⟨fun r f =>
    { toFun := fun m => algebraMap R A r • f m
      map_add' := fun m m' => by rw [map_add, smul_add]
      map_smul' := fun a m => by
        simp only [RingHom.id_apply, map_smul, smul_smul, Algebra.commutes]
      map_mem' := fun hm => by
        simpa using smul_mem_grading (algebraMap_mem_grading R (A := A) r) (f.map_mem hm)
      map_d' := fun m => by
        simp only [map_d, d_smul (algebraMap_mem_grading R (A := A) r), d_algebraMap, zero_smul,
          zero_add, koszulSign, Int.negOnePow_zero, one_smul] }⟩

/--
@isnad1 id=eq.0h7v.s8.2f9acafecc59 from=translated src=- shape=d207b578 vocab=b8437d15
-/
@[simp]
theorem smul_apply (r : R) (f : M →ᵈᵍ[A] N) (m : M) : (r • f) m = algebraMap R A r • f m := rfl

/-- `M →ᵈᵍ[A] N` is an `R`-module for a dg `R`-algebra `A`.-/
instance (priority := 100) instModule : Module R (M →ᵈᵍ[A] N) where
  one_smul f := ext fun m => by simp
  mul_smul r s f := ext fun m => by simp [mul_smul]
  smul_zero r := ext fun m => by simp
  smul_add r f g := ext fun m => by simp
  add_smul r s f := ext fun m => by simp [add_smul]
  zero_smul f := ext fun m => by simp

omit [DGModule A N] in
/--
@isnad1 id=eq.0h8v.s9.c3f681450331 from=translated src=- shape=716cfe06 vocab=1775ac4c
-/
theorem smul_comp (r : R) (g : N →ᵈᵍ[A] P) (f : M →ᵈᵍ[A] N) : (r • g).comp f = r • g.comp f :=
  rfl

/--
@isnad1 id=eq.0h8v.s9.a1626ae63a05 from=translated src=- shape=6e5e25ff vocab=1775ac4c
-/
theorem comp_smul (r : R) (g : N →ᵈᵍ[A] P) (f : M →ᵈᵍ[A] N) : g.comp (r • f) = r • g.comp f :=
  ext fun m => by simp

end DGModuleHom

namespace DGModuleCat

variable {A} {R : Type*} [CommRing R] [Algebra R A] [DGRing A] [DGAlgebra R A]

/-- The action of `R` on the morphisms of `DGModuleCat A` for a dg `R`-algebra `A`.-/
instance (priority := 100) instSMulHom {M N : DGModuleCat.{v} A} : SMul R (M ⟶ N) where
  smul r f := ⟨r • f.hom⟩

/--
@isnad1 id=eq.0h6v.s10.265d71902301 from=translated src=- shape=d507ed04 vocab=1e67cdd8
-/
@[simp]
theorem hom_smul {M N : DGModuleCat.{v} A} (r : R) (f : M ⟶ N) : (r • f).hom = r • f.hom := rfl

/--
@isnad1 id=eq.0h7v.s9.9b0339187f41 from=translated src=- shape=8a37a766 vocab=4d4e9a14
-/
@[simp]
theorem smul_apply {M N : DGModuleCat.{v} A} (r : R) (f : M ⟶ N) (x : M) :
    (r • f) x = algebraMap R A r • f x := rfl

/-- `DGModuleCat A` is an `R`-linear category for a dg `R`-algebra `A`.-/
instance (priority := 100) instLinear : Linear R (DGModuleCat.{v} A) where
  homModule M N := Function.Injective.module R
    { toFun := Hom.hom, map_zero' := hom_zero, map_add' := hom_add } hom_injective
    fun _ _ => rfl
  smul_comp _ _ _ _ _ _ := hom_ext_apply fun _ => by simp only [comp_apply, smul_apply, map_smul]
  comp_smul _ _ _ _ _ _ := hom_ext_apply fun _ => by simp only [comp_apply, smul_apply]

end DGModuleCat

end DG
