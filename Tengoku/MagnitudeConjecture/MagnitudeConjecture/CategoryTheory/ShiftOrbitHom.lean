import Tengoku.Seed.Algebra.DirectSum.Module
import Tengoku.Seed.CategoryTheory.Preadditive.AdditiveFunctor
import Tengoku.Seed.CategoryTheory.Shift.ShiftedHom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Homogeneous morphisms for a shift orbit category

Mathlib's `HasShift` is a coherent action of an additive monoid by
endofunctors.  For a group action written additively, the homogeneous
degree-`a` orbit morphisms from `X` to `Y` are the morphisms
`X ⟶ Y⟦a⟧`.  This file defines their identity and composition and proves
the unit and associativity laws before passing to direct sums.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v w

variable {C : Type u} [Category.{v} C]
variable {A : Type w} [AddMonoid A] [HasShift C A]

/-- Homogeneous orbit morphisms of degree `a`.-/
abbrev ShiftHom (X Y : C) (a : A) := X ⟶ (shiftFunctor C a).obj Y

/-- The degree-zero homogeneous identity.-/
def shiftHomId (X : C) : ShiftHom X X (0 : A) :=
  (shiftFunctorZero C A).inv.app X

/-- An ordinary morphism regarded as a degree-zero homogeneous morphism.-/
def shiftHomZero {X Y : C} (f : X ⟶ Y) : ShiftHom X Y (0 : A) :=
  CategoryTheory.ShiftedHom.mk₀ 0 rfl f

/--
@isnad1 id=eq.0h3v.s5.c932bb707482 from=translated src=- shape=d07ee2bc vocab=9668f84e
-/
@[simp]
theorem shiftHomZero_id (X : C) :
    shiftHomZero (A := A) (𝟙 X) = shiftHomId X := by
  simp [shiftHomZero, shiftHomId, CategoryTheory.ShiftedHom.mk₀,
    shiftFunctorZero']

/-- Composition of homogeneous orbit morphisms, with an explicitly chosen
output degree.  The order `b + a` comes from applying the degree-`a` shift to
a degree-`b` second morphism.-/
def shiftHomComp'
    {X Y Z : C} {a b c : A} (h : b + a = c)
    (f : ShiftHom X Y a) (g : ShiftHom Y Z b) : ShiftHom X Z c :=
  f ≫ (shiftFunctor C a).map g ≫
    (shiftFunctorAdd' C b a c h).inv.app Z

/-- Composition with its canonical output degree.-/
def shiftHomComp
    {X Y Z : C} {a b : A}
    (f : ShiftHom X Y a) (g : ShiftHom Y Z b) :
    ShiftHom X Z (b + a) :=
  shiftHomComp' rfl f g

/-- Canonical homogeneous composition agrees heterogeneously with composition
at any propositionally equal output degree.
@isnad1 id=heq.1h10v.s6.76bc36b6441c from=translated src=- shape=fc14b7a4 vocab=ff191d42
-/
theorem shiftHomComp_heq_shiftHomComp'
    {X Y Z : C} {a b c : A} (h : b + a = c)
    (f : ShiftHom X Y a) (g : ShiftHom Y Z b) :
    HEq (shiftHomComp f g) (shiftHomComp' h f g) := by
  subst c
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h7v.s7.2f9dc0d8f958 from=translated src=- shape=06356649 vocab=4bbfecb6
-/
@[simp]
theorem shiftHomComp'_zero_zero
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    shiftHomComp' (zero_add (0 : A))
        (shiftHomZero (A := A) f) (shiftHomZero (A := A) g) =
      shiftHomZero (A := A) (f ≫ g) := by
  simpa [shiftHomComp', shiftHomZero, CategoryTheory.ShiftedHom.comp] using
    CategoryTheory.ShiftedHom.mk₀_comp_mk₀ f g (zero_add (0 : A)) rfl rfl

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h6v.s6.29b42647b94c from=translated src=- shape=caa962cf vocab=cc337463
-/
@[simp]
theorem shiftHomComp'_id_left
    {X Y : C} {a : A} (f : ShiftHom X Y a) :
    shiftHomComp' (add_zero a) (shiftHomId X) f = f := by
  simp only [shiftHomComp', shiftHomId,
    shiftFunctorAdd'_add_zero_inv_app]
  rw [(shiftFunctorZero C A).hom.naturality]
  simp

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h6v.s6.66d33772c079 from=translated src=- shape=68703ccc vocab=e9bbee4a
-/
@[simp]
theorem shiftHomComp'_id_right
    {X Y : C} {a : A} (f : ShiftHom X Y a) :
    shiftHomComp' (zero_add a) f (shiftHomId Y) = f := by
  simp only [shiftHomComp', shiftHomId,
    shiftFunctorAdd'_zero_add_inv_app]
  rw [← Functor.map_comp]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Associativity of homogeneous composition, including all degree
reassociations.
@isnad1 id=eq.4h15v.s7.969bc5d7309e from=translated src=- shape=b530c05a vocab=a025ebef
-/
theorem shiftHomComp'_assoc
    {W X Y Z : C} {a b c ba cb d : A}
    (hba : b + a = ba) (hcb : c + b = cb)
    (hleft : c + ba = d) (hright : cb + a = d)
    (f : ShiftHom W X a) (g : ShiftHom X Y b)
    (h : ShiftHom Y Z c) :
    shiftHomComp' hleft (shiftHomComp' hba f g) h =
      shiftHomComp' hright f (shiftHomComp' hcb g h) := by
  subst ba
  subst cb
  subst d
  have hright_eq : hright = add_assoc c b a := Subsingleton.elim _ _
  rw [hright_eq]
  simp only [shiftHomComp', Functor.map_comp, Category.assoc]
  rw [← (shiftFunctorAdd' C b a (b + a) rfl).inv.naturality_assoc h]
  rw [shiftFunctorAdd'_assoc_inv_app c b a (c + b) (b + a)
    (c + (b + a)) rfl rfl (add_assoc c b a)]
  rfl

section DirectSum

variable [Preadditive C]
variable [∀ a : A, (shiftFunctor C a).Additive]

/-- The finite-support direct sum of all homogeneous shift morphisms.-/
abbrev ShiftOrbitHom (A : Type w) [AddMonoid A] [HasShift C A]
    (X Y : C) := DirectSum A (fun a ↦ ShiftHom X Y a)

/-- Inclusion of one homogeneous component into the orbit Hom direct sum.-/
noncomputable def shiftOrbitOf (X Y : C) (a : A) :
    ShiftHom X Y a →+ ShiftOrbitHom A X Y := by
  classical
  exact DirectSum.of (fun c : A ↦ ShiftHom X Y c) a

omit [∀ a : A, (shiftFunctor C a).Additive] in
/-- With a fixed decidable equality on the degree monoid, the homogeneous
inclusion is the corresponding direct-sum generator.
@isnad1 id=eq.0h6v.s10.4c2471ee38fe from=translated src=- shape=0e5aae05 vocab=3992b7a0
-/
theorem shiftOrbitOf_eq_directSumOf [DecidableEq A]
    (X Y : C) (a : A) (f : ShiftHom X Y a) :
    shiftOrbitOf X Y a f =
      DirectSum.of (fun c : A ↦ ShiftHom X Y c) a f := by
  unfold shiftOrbitOf
  have h : (fun b c : A ↦ Classical.propDecidable (b = c)) =
      (inferInstance : DecidableEq A) :=
    Subsingleton.elim _ _
  rw [h]

/-- Homogeneous composition as a homomorphism in both variables.-/
def shiftHomCompAddHom
    {X Y Z : C} {a b : A} :
    ShiftHom X Y a →+ ShiftHom Y Z b →+ ShiftHom X Z (b + a) where
  toFun f :=
    { toFun := fun g ↦ shiftHomComp f g
      map_zero' := by simp [shiftHomComp, shiftHomComp']
      map_add' := by
        intro g h
        simp [shiftHomComp, shiftHomComp', Functor.map_add,
          Preadditive.comp_add] }
  map_zero' := by
    ext g
    simp [shiftHomComp, shiftHomComp']
  map_add' := by
    intro f g
    ext h
    simp [shiftHomComp, shiftHomComp', Preadditive.add_comp]

section Linear

variable {k : Type*} [CommSemiring k] [CategoryTheory.Linear k C]
variable [∀ a : A, (shiftFunctor C a).Linear k]

omit [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k] in
/--
@isnad1 id=eq.0h7v.s9.bd509e8037f1 from=translated src=- shape=76d4db19 vocab=8ed31820
-/
@[simp]
theorem shiftHomZero_smul
    {X Y : C} (r : k) (f : X ⟶ Y) :
    shiftHomZero (A := A) (r • f) = r • shiftHomZero (A := A) f := by
  simp [shiftHomZero, CategoryTheory.ShiftedHom.mk₀,
    CategoryTheory.Linear.smul_comp]

omit [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k] in
/--
@isnad1 id=eq.0h11v.s10.88191bbb5848 from=translated src=- shape=3bbb38d9 vocab=b431e543
-/
@[simp]
theorem shiftHomComp_smul_left
    {X Y Z : C} {a b : A} (r : k)
    (f : ShiftHom X Y a) (g : ShiftHom Y Z b) :
    shiftHomComp (r • f) g = r • shiftHomComp f g := by
  simp [shiftHomComp, shiftHomComp', CategoryTheory.Linear.smul_comp]

omit [∀ a : A, (shiftFunctor C a).Additive] in
/--
@isnad1 id=eq.0h11v.s10.3270957d8067 from=translated src=- shape=f3a62074 vocab=1ff249df
-/
@[simp]
theorem shiftHomComp_smul_right
    {X Y Z : C} {a b : A} (r : k)
    (f : ShiftHom X Y a) (g : ShiftHom Y Z b) :
    shiftHomComp f (r • g) = r • shiftHomComp f g := by
  simp [shiftHomComp, shiftHomComp', Functor.map_smul,
    CategoryTheory.Linear.comp_smul]

/-- Homogeneous composition as a linear map in both variables.-/
def shiftHomCompLinearMap
    {X Y Z : C} {a b : A} :
    ShiftHom X Y a →ₗ[k] ShiftHom Y Z b →ₗ[k] ShiftHom X Z (b + a) :=
  LinearMap.mk₂ k shiftHomComp
    (fun f g h ↦ DFunLike.congr_fun (shiftHomCompAddHom.map_add f g) h)
    (fun r _ _ ↦ shiftHomComp_smul_left r _ _)
    (fun f g h ↦ (shiftHomCompAddHom f).map_add g h)
    (fun r _ _ ↦ shiftHomComp_smul_right r _ _)

/-- Linear inclusion of one homogeneous component into the orbit Hom direct
sum.-/
noncomputable def shiftOrbitLof (X Y : C) (a : A) :
    ShiftHom X Y a →ₗ[k] ShiftOrbitHom A X Y := by
  classical
  exact DirectSum.lof k A (fun c : A ↦ ShiftHom X Y c) a

omit [∀ a : A, (shiftFunctor C a).Additive]
  [∀ a : A, (shiftFunctor C a).Linear k] in
/--
@isnad1 id=eq.0h7v.s9.c2494980faf9 from=translated src=- shape=aa1278bf vocab=fe4951a1
-/
@[simp]
theorem shiftOrbitLof_apply
    {X Y : C} {a : A} (f : ShiftHom X Y a) :
    shiftOrbitLof (k := k) X Y a f = shiftOrbitOf X Y a f := by
  rfl

/-- Homogeneous composition followed by inclusion in the output direct sum.-/
def shiftHomCompLofLinearMap
    {X Y Z : C} (a b : A) :
    ShiftHom X Y a →ₗ[k] ShiftHom Y Z b →ₗ[k] ShiftOrbitHom A X Z :=
  LinearMap.mk₂ k
    (fun f g ↦ shiftOrbitLof (k := k) X Z (b + a) (shiftHomComp f g))
    (fun f₁ f₂ g ↦ by
      rw [show shiftHomComp (f₁ + f₂) g =
        shiftHomComp f₁ g + shiftHomComp f₂ g from
          DFunLike.congr_fun (shiftHomCompAddHom.map_add f₁ f₂) g]
      exact (shiftOrbitLof (k := k) X Z (b + a)).map_add _ _)
    (fun r f g ↦ by
      rw [shiftHomComp_smul_left]
      exact (shiftOrbitLof (k := k) X Z (b + a)).map_smul r _)
    (fun f g₁ g₂ ↦ by
      have hcomp : shiftHomComp f (g₁ + g₂) =
          shiftHomComp f g₁ + shiftHomComp f g₂ :=
        (shiftHomCompAddHom f).map_add g₁ g₂
      rw [hcomp]
      exact (shiftOrbitLof (k := k) X Z (b + a)).map_add _ _)
    (fun r f g ↦ by
      rw [shiftHomComp_smul_right]
      exact (shiftOrbitLof (k := k) X Z (b + a)).map_smul r _)

/-- Convolution as a linear map in both direct-sum variables.-/
noncomputable def shiftOrbitCompLinearMap
    {X Y Z : C} :
    ShiftOrbitHom A X Y →ₗ[k]
      ShiftOrbitHom A Y Z →ₗ[k] ShiftOrbitHom A X Z := by
  classical
  exact
    DirectSum.toModule k A _ fun a ↦
      (DirectSum.toModule k A _ fun b ↦
        (shiftHomCompLofLinearMap (k := k) (X := X) (Y := Y) (Z := Z) a b).flip).flip

/--
@isnad1 id=eq.0h10v.s12.0ad0dd91de84 from=translated src=- shape=45696c76 vocab=10387444
-/
@[simp]
theorem shiftOrbitCompLinearMap_of_of
    {X Y Z : C} {a b : A}
    (f : ShiftHom X Y a) (g : ShiftHom Y Z b) :
    shiftOrbitCompLinearMap (k := k)
        (shiftOrbitOf X Y a f) (shiftOrbitOf Y Z b g) =
      shiftOrbitOf X Z (b + a) (shiftHomComp f g) := by
  classical
  change shiftOrbitCompLinearMap (k := k)
      (DirectSum.lof k A (fun c : A ↦ ShiftHom X Y c) a f)
      (DirectSum.lof k A (fun c : A ↦ ShiftHom Y Z c) b g) =
    shiftOrbitLof (k := k) X Z (b + a) (shiftHomComp f g)
  simp [shiftOrbitCompLinearMap, shiftHomCompLofLinearMap]

end Linear

/-- Convolution composition on finite-support direct sums of homogeneous
morphisms.-/
def shiftOrbitCompHom
    {X Y Z : C} :
    ShiftOrbitHom A X Y →+ ShiftOrbitHom A Y Z →+ ShiftOrbitHom A X Z := by
  classical
  exact
    DirectSum.toAddMonoid fun a ↦
      AddMonoidHom.flip <|
        DirectSum.toAddMonoid fun b ↦
          AddMonoidHom.flip <|
            (shiftOrbitOf X Z (b + a)).compHom.comp shiftHomCompAddHom

section LinearComparison

variable {k : Type*} [CommSemiring k] [CategoryTheory.Linear k C]
variable [∀ a : A, (shiftFunctor C a).Linear k]

end LinearComparison

/-- Identity morphism in the shift-orbit Hom direct sum.-/
def shiftOrbitId (X : C) : ShiftOrbitHom A X X :=
  shiftOrbitOf X X 0 (shiftHomId X)

/-- The shift-orbit category has the same objects as `C` and finite-support
direct sums of shifted Hom spaces as morphisms.-/
@[nolint unusedArguments]
def ShiftOrbitCategory (C : Type u) (_A : Type w) := C

namespace ShiftOrbitCategory

instance categoryStruct : CategoryStruct.{max v w} (ShiftOrbitCategory C A) where
  Hom X Y := ShiftOrbitHom (C := C) A (show C from X) (show C from Y)
  id X := shiftOrbitId (C := C) (A := A) (show C from X)
  comp f g := shiftOrbitCompHom (C := C) (A := A) f g

section LinearCategory

variable {k : Type*} [CommSemiring k] [CategoryTheory.Linear k C]
variable [∀ a : A, (shiftFunctor C a).Linear k]

end LinearCategory

end ShiftOrbitCategory

end DirectSum

end MagnitudeConjecture.CoveringHom
