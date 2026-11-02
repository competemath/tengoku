/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.KTheory.Presentation
import Tengoku.Seed.Algebra.Ring.MinimalAxioms

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bilinear products on exact Grothendieck groups

A tensor product which preserves exact triples in each variable descends to a bilinear product
on the presented Grothendieck group.  This is the multiplicative foundation needed for the
ring structure on `K₀` and for multiplicativity of the Chern character.

The construction uses the universal property twice.  It does not impose associativity, a unit,
or commutativity: those laws can subsequently be proved from the corresponding geometric tensor
isomorphisms without contaminating the additive quotient construction.
-/

noncomputable section

universe u v

namespace ExactGrothendieck

variable {Object : Type u} {Exact : Object → Object → Object → Prop}

/-- Multiplication by an object on the left, descended through exact triples in the right
variable.-/
def leftObjectMul (tensor : Object → Object → Object)
    (exactRight : ∀ X A B C, Exact A B C →
      Exact (tensor X A) (tensor X B) (tensor X C))
    (X : Object) : Group Object Exact →+ Group Object Exact :=
  lift (fun Y ↦ classOf Object Exact (tensor X Y)) fun A B C h ↦
    classOf_middle Object Exact _ _ _ (exactRight X A B C h)

@[simp]
theorem leftObjectMul_classOf (tensor : Object → Object → Object)
    (exactRight : ∀ X A B C, Exact A B C →
      Exact (tensor X A) (tensor X B) (tensor X C))
    (X Y : Object) :
    leftObjectMul tensor exactRight X (classOf Object Exact Y) =
      classOf Object Exact (tensor X Y) :=
  lift_classOf _ _ _

/-- The first-variable universal lift.  Its value is an additive endomorphism because the
second-variable quotient was already performed by `leftObjectMul`.-/
def productHom (tensor : Object → Object → Object)
    (exactLeft : ∀ A B C Y, Exact A B C →
      Exact (tensor A Y) (tensor B Y) (tensor C Y))
    (exactRight : ∀ X A B C, Exact A B C →
      Exact (tensor X A) (tensor X B) (tensor X C)) :
    Group Object Exact →+ (Group Object Exact →+ Group Object Exact) :=
  lift (fun X ↦ leftObjectMul tensor exactRight X) fun A B C h ↦ by
    apply hom_ext Object Exact
    intro Y
    simp only [leftObjectMul_classOf, AddMonoidHom.add_apply]
    exact classOf_middle Object Exact _ _ _ (exactLeft A B C Y h)

/-- The bilinear product induced on the exact Grothendieck group.-/
def product (tensor : Object → Object → Object)
    (exactLeft : ∀ A B C Y, Exact A B C →
      Exact (tensor A Y) (tensor B Y) (tensor C Y))
    (exactRight : ∀ X A B C, Exact A B C →
      Exact (tensor X A) (tensor X B) (tensor X C))
    (x y : Group Object Exact) : Group Object Exact :=
  productHom tensor exactLeft exactRight x y

@[simp]
theorem product_classOf_left (tensor : Object → Object → Object)
    (exactLeft : ∀ A B C Y, Exact A B C →
      Exact (tensor A Y) (tensor B Y) (tensor C Y))
    (exactRight : ∀ X A B C, Exact A B C →
      Exact (tensor X A) (tensor X B) (tensor X C))
    (X : Object) (y : Group Object Exact) :
    product tensor exactLeft exactRight (classOf Object Exact X) y =
      leftObjectMul tensor exactRight X y := by
  simp [product, productHom]

@[simp]
theorem product_classOf_classOf (tensor : Object → Object → Object)
    (exactLeft : ∀ A B C Y, Exact A B C →
      Exact (tensor A Y) (tensor B Y) (tensor C Y))
    (exactRight : ∀ X A B C, Exact A B C →
      Exact (tensor X A) (tensor X B) (tensor X C))
    (X Y : Object) :
    product tensor exactLeft exactRight
        (classOf Object Exact X) (classOf Object Exact Y) =
      classOf Object Exact (tensor X Y) := by
  rw [product_classOf_left, leftObjectMul_classOf]

theorem product_add_left (tensor : Object → Object → Object)
    (exactLeft : ∀ A B C Y, Exact A B C →
      Exact (tensor A Y) (tensor B Y) (tensor C Y))
    (exactRight : ∀ X A B C, Exact A B C →
      Exact (tensor X A) (tensor X B) (tensor X C))
    (x y z : Group Object Exact) :
    product tensor exactLeft exactRight (x + y) z =
      product tensor exactLeft exactRight x z +
        product tensor exactLeft exactRight y z := by
  change productHom tensor exactLeft exactRight (x + y) z = _
  rw [map_add]
  rfl

theorem product_add_right (tensor : Object → Object → Object)
    (exactLeft : ∀ A B C Y, Exact A B C →
      Exact (tensor A Y) (tensor B Y) (tensor C Y))
    (exactRight : ∀ X A B C, Exact A B C →
      Exact (tensor X A) (tensor X B) (tensor X C))
    (x y z : Group Object Exact) :
    product tensor exactLeft exactRight x (y + z) =
      product tensor exactLeft exactRight x y +
        product tensor exactLeft exactRight x z := by
  exact map_add (productHom tensor exactLeft exactRight x) y z

@[simp]
theorem product_zero_left (tensor : Object → Object → Object)
    (exactLeft : ∀ A B C Y, Exact A B C →
      Exact (tensor A Y) (tensor B Y) (tensor C Y))
    (exactRight : ∀ X A B C, Exact A B C →
      Exact (tensor X A) (tensor X B) (tensor X C))
    (y : Group Object Exact) :
    product tensor exactLeft exactRight 0 y = 0 := by
  change productHom tensor exactLeft exactRight 0 y = 0
  rw [map_zero]
  rfl

@[simp]
theorem product_zero_right (tensor : Object → Object → Object)
    (exactLeft : ∀ A B C Y, Exact A B C →
      Exact (tensor A Y) (tensor B Y) (tensor C Y))
    (exactRight : ∀ X A B C, Exact A B C →
      Exact (tensor X A) (tensor X B) (tensor X C))
    (x : Group Object Exact) :
    product tensor exactLeft exactRight x 0 = 0 :=
  map_zero (productHom tensor exactLeft exactRight x)

/-- Multiplication by a fixed virtual class on the right.-/
def rightMul (tensor : Object → Object → Object)
    (exactLeft : ∀ A B C Y, Exact A B C →
      Exact (tensor A Y) (tensor B Y) (tensor C Y))
    (exactRight : ∀ X A B C, Exact A B C →
      Exact (tensor X A) (tensor X B) (tensor X C))
    (y : Group Object Exact) : Group Object Exact →+ Group Object Exact where
  toFun x := product tensor exactLeft exactRight x y
  map_zero' := product_zero_left tensor exactLeft exactRight y
  map_add' x z := product_add_left tensor exactLeft exactRight x z y

@[simp]
theorem rightMul_apply (tensor : Object → Object → Object)
    (exactLeft : ∀ A B C Y, Exact A B C →
      Exact (tensor A Y) (tensor B Y) (tensor C Y))
    (exactRight : ∀ X A B C, Exact A B C →
      Exact (tensor X A) (tensor X B) (tensor X C))
    (x y : Group Object Exact) :
    rightMul tensor exactLeft exactRight y x = product tensor exactLeft exactRight x y :=
  rfl

/-- The same bilinear product with its two virtual inputs exchanged.-/
def flipProductHom (tensor : Object → Object → Object)
    (exactLeft : ∀ A B C Y, Exact A B C →
      Exact (tensor A Y) (tensor B Y) (tensor C Y))
    (exactRight : ∀ X A B C, Exact A B C →
      Exact (tensor X A) (tensor X B) (tensor X C)) :
    Group Object Exact →+ (Group Object Exact →+ Group Object Exact) where
  toFun := rightMul tensor exactLeft exactRight
  map_zero' := by
    apply AddMonoidHom.ext
    intro x
    exact product_zero_right tensor exactLeft exactRight x
  map_add' y z := by
    apply AddMonoidHom.ext
    intro x
    exact product_add_right tensor exactLeft exactRight x y z

@[simp]
theorem flipProductHom_apply (tensor : Object → Object → Object)
    (exactLeft : ∀ A B C Y, Exact A B C →
      Exact (tensor A Y) (tensor B Y) (tensor C Y))
    (exactRight : ∀ X A B C, Exact A B C →
      Exact (tensor X A) (tensor X B) (tensor X C))
    (x y : Group Object Exact) :
    flipProductHom tensor exactLeft exactRight x y =
      product tensor exactLeft exactRight y x :=
  rfl

/-- Associativity on object classes propagates to associativity on every virtual class.-/
theorem product_assoc_of_classOf (tensor : Object → Object → Object)
    (exactLeft : ∀ A B C Y, Exact A B C →
      Exact (tensor A Y) (tensor B Y) (tensor C Y))
    (exactRight : ∀ X A B C, Exact A B C →
      Exact (tensor X A) (tensor X B) (tensor X C))
    (hassoc : ∀ X Y Z,
      classOf Object Exact (tensor (tensor X Y) Z) =
        classOf Object Exact (tensor X (tensor Y Z)))
    (x y z : Group Object Exact) :
    product tensor exactLeft exactRight
        (product tensor exactLeft exactRight x y) z =
      product tensor exactLeft exactRight x
        (product tensor exactLeft exactRight y z) := by
  have hObjects (X Y : Object) :
      leftObjectMul tensor exactRight (tensor X Y) =
        (leftObjectMul tensor exactRight X).comp
          (leftObjectMul tensor exactRight Y) := by
    apply hom_ext Object Exact
    intro Z
    simp only [leftObjectMul_classOf, AddMonoidHom.comp_apply]
    exact hassoc X Y Z
  have hOneObject (X : Object) :
      (rightMul tensor exactLeft exactRight z).comp
          (leftObjectMul tensor exactRight X) =
        (leftObjectMul tensor exactRight X).comp
          (rightMul tensor exactLeft exactRight z) := by
    apply hom_ext Object Exact
    intro Y
    have h := congrArg (fun f : Group Object Exact →+ Group Object Exact => f z)
      (hObjects X Y)
    simpa only [AddMonoidHom.comp_apply, leftObjectMul_classOf, rightMul_apply,
      product_classOf_left] using h
  have hAll :
      (rightMul tensor exactLeft exactRight z).comp
          (rightMul tensor exactLeft exactRight y) =
        rightMul tensor exactLeft exactRight
          (product tensor exactLeft exactRight y z) := by
    apply hom_ext Object Exact
    intro X
    have h := congrArg (fun f : Group Object Exact →+ Group Object Exact => f y)
      (hOneObject X)
    simpa only [AddMonoidHom.comp_apply, rightMul_apply, product_classOf_left] using h
  exact congrArg (fun f : Group Object Exact →+ Group Object Exact => f x) hAll

/-- Commutativity on object classes propagates to commutativity on every virtual class.-/
theorem product_comm_of_classOf (tensor : Object → Object → Object)
    (exactLeft : ∀ A B C Y, Exact A B C →
      Exact (tensor A Y) (tensor B Y) (tensor C Y))
    (exactRight : ∀ X A B C, Exact A B C →
      Exact (tensor X A) (tensor X B) (tensor X C))
    (hcomm : ∀ X Y,
      classOf Object Exact (tensor X Y) = classOf Object Exact (tensor Y X))
    (x y : Group Object Exact) :
    product tensor exactLeft exactRight x y =
      product tensor exactLeft exactRight y x := by
  have h : productHom tensor exactLeft exactRight =
      flipProductHom tensor exactLeft exactRight := by
    apply hom_ext Object Exact
    intro X
    apply hom_ext Object Exact
    intro Y
    simp only [productHom, lift_classOf, leftObjectMul_classOf, flipProductHom_apply,
      product_classOf_classOf]
    exact hcomm X Y
  exact congrArg (fun f : Group Object Exact →+ (Group Object Exact →+ Group Object Exact) =>
    f x y) h

/-- A left-unit law on object classes propagates to every virtual class.-/
theorem product_one_left_of_classOf (tensor : Object → Object → Object)
    (exactLeft : ∀ A B C Y, Exact A B C →
      Exact (tensor A Y) (tensor B Y) (tensor C Y))
    (exactRight : ∀ X A B C, Exact A B C →
      Exact (tensor X A) (tensor X B) (tensor X C))
    (unit : Object)
    (hunit : ∀ X, classOf Object Exact (tensor unit X) = classOf Object Exact X)
    (x : Group Object Exact) :
    product tensor exactLeft exactRight (classOf Object Exact unit) x = x := by
  have h : leftObjectMul tensor exactRight unit =
      AddMonoidHom.id (Group Object Exact) := by
    apply hom_ext Object Exact
    intro X
    simpa only [leftObjectMul_classOf, AddMonoidHom.id_apply] using hunit X
  simpa only [product_classOf_left, AddMonoidHom.id_apply] using
    congrArg (fun f : Group Object Exact →+ Group Object Exact => f x) h

/-- A right-unit law on object classes propagates to every virtual class.-/
theorem product_one_right_of_classOf (tensor : Object → Object → Object)
    (exactLeft : ∀ A B C Y, Exact A B C →
      Exact (tensor A Y) (tensor B Y) (tensor C Y))
    (exactRight : ∀ X A B C, Exact A B C →
      Exact (tensor X A) (tensor X B) (tensor X C))
    (unit : Object)
    (hunit : ∀ X, classOf Object Exact (tensor X unit) = classOf Object Exact X)
    (x : Group Object Exact) :
    product tensor exactLeft exactRight x (classOf Object Exact unit) = x := by
  have h : rightMul tensor exactLeft exactRight (classOf Object Exact unit) =
      AddMonoidHom.id (Group Object Exact) := by
    apply hom_ext Object Exact
    intro X
    simpa only [rightMul_apply, product_classOf_classOf, AddMonoidHom.id_apply] using hunit X
  simpa only [rightMul_apply, AddMonoidHom.id_apply] using
    congrArg (fun f : Group Object Exact →+ Group Object Exact => f x) h

/-- Object-level tensor data sufficient to make the exact Grothendieck group a commutative
ring.  All laws are required only on object classes; the quotient-generation theorems above
propagate them to arbitrary virtual classes.-/
structure CommutativeTensorData (Object : Type u) (Exact : Object → Object → Object → Prop)
    where
  /-- Tensor product on geometric objects.-/
  tensor : Object → Object → Object
  /-- Tensoring in the left variable preserves exact triples.-/
  exactLeft : ∀ A B C Y, Exact A B C →
    Exact (tensor A Y) (tensor B Y) (tensor C Y)
  /-- Tensoring in the right variable preserves exact triples.-/
  exactRight : ∀ X A B C, Exact A B C →
    Exact (tensor X A) (tensor X B) (tensor X C)
  /-- Tensor product is associative on object classes.-/
  assocClass : ∀ X Y Z,
    classOf Object Exact (tensor (tensor X Y) Z) =
      classOf Object Exact (tensor X (tensor Y Z))
  /-- Tensor product is symmetric on object classes.-/
  commClass : ∀ X Y,
    classOf Object Exact (tensor X Y) = classOf Object Exact (tensor Y X)
  /-- Tensor unit.-/
  unit : Object
  /-- The tensor unit acts on the left on object classes.-/
  unitClass : ∀ X,
    classOf Object Exact (tensor unit X) = classOf Object Exact X

namespace CommutativeTensorData

variable (T : CommutativeTensorData Object Exact)

/-- Multiplication on virtual classes induced by the tensor data.-/
noncomputable def mul (x y : Group Object Exact) : Group Object Exact :=
  product T.tensor T.exactLeft T.exactRight x y

/-- The tensor unit as a virtual object class.-/
noncomputable def one : Group Object Exact :=
  classOf Object Exact T.unit

/-- The exact Grothendieck group carries a genuine commutative-ring structure whenever the
selected geometric objects have exact symmetric tensor data.-/
@[reducible] noncomputable def commRing : CommRing (Group Object Exact) := by
  letI : Mul (Group Object Exact) := ⟨T.mul⟩
  letI : One (Group Object Exact) := ⟨T.one⟩
  exact CommRing.ofMinimalAxioms
    add_assoc zero_add neg_add_cancel
    (product_assoc_of_classOf T.tensor T.exactLeft T.exactRight T.assocClass)
    (product_comm_of_classOf T.tensor T.exactLeft T.exactRight T.commClass)
    (product_one_left_of_classOf T.tensor T.exactLeft T.exactRight T.unit T.unitClass)
    (product_add_right T.tensor T.exactLeft T.exactRight)

/-- The multiplication field of `commRing` is the independently constructed quotient product.-/
theorem commRing_mul_eq (x y : Group Object Exact) :
    @Mul.mul (Group Object Exact) T.commRing.toMul x y = T.mul x y :=
  rfl

/-- The unit field of `commRing` is the class of the geometric tensor unit.-/
theorem commRing_one_eq :
    @OfNat.ofNat (Group Object Exact) 1 T.commRing.toOfNat1 = T.one :=
  rfl

/-- An exact-additive object invariant which is multiplicative on tensor products is
multiplicative on all virtual classes.-/
theorem lift_product {A : Type v} [CommRing A] (c : Object → A)
    (hadd : ∀ X Y Z, Exact X Y Z → c Y = c X + c Z)
    (hmul : ∀ X Y, c (T.tensor X Y) = c X * c Y)
    (x y : Group Object Exact) :
    lift c hadd (T.mul x y) = lift c hadd x * lift c hadd y := by
  let L := lift c hadd
  let rObject (X : Object) : Group Object Exact →+ A := {
    toFun := fun z ↦ c X * L z
    map_zero' := by simp
    map_add' := by simp [mul_add] }
  have hObject (X : Object) :
      L.comp (leftObjectMul T.tensor T.exactRight X) = rObject X := by
    apply hom_ext Object Exact
    intro Y
    simp only [AddMonoidHom.comp_apply, leftObjectMul_classOf]
    change L (classOf Object Exact (T.tensor X Y)) =
      rObject X (classOf Object Exact Y)
    rw [show rObject X (classOf Object Exact Y) =
      c X * L (classOf Object Exact Y) from rfl]
    simp only [L, lift_classOf]
    exact hmul X Y
  let rAll : Group Object Exact →+ A := {
    toFun := fun z ↦ L z * L y
    map_zero' := by simp
    map_add' := by simp [add_mul] }
  have hAll :
      L.comp (rightMul T.tensor T.exactLeft T.exactRight y) = rAll := by
    apply hom_ext Object Exact
    intro X
    have h := congrArg (fun f : Group Object Exact →+ A ↦ f y) (hObject X)
    change L (T.mul (classOf Object Exact X) y) =
      L (classOf Object Exact X) * L y
    rw [CommutativeTensorData.mul, product_classOf_left]
    rw [show L (classOf Object Exact X) = c X by
      simp only [L, lift_classOf]]
    change L (leftObjectMul T.tensor T.exactRight X y) = rObject X y at h
    rw [show rObject X y = c X * L y from rfl] at h
    exact h
  exact congrArg (fun f : Group Object Exact →+ A ↦ f x) hAll

/-- An exact-additive object invariant normalized on the tensor unit sends the virtual tensor
unit to one.-/
theorem lift_one {A : Type v} [CommRing A] (c : Object → A)
    (hadd : ∀ X Y Z, Exact X Y Z → c Y = c X + c Z)
    (hone : c T.unit = 1) : lift c hadd T.one = 1 := by
  change lift c hadd (classOf Object Exact T.unit) = 1
  rw [lift_classOf]
  exact hone

/-- Left unit law for every virtual class.-/
theorem one_mul (x : Group Object Exact) : T.mul T.one x = x :=
  product_one_left_of_classOf T.tensor T.exactLeft T.exactRight T.unit T.unitClass x

/-- Right unit law for every virtual class, obtained from the left unit by commutativity on
object classes.-/
theorem mul_one (x : Group Object Exact) : T.mul x T.one = x := by
  rw [mul, one, product_comm_of_classOf T.tensor T.exactLeft T.exactRight T.commClass,
    ← one, ← mul, one_mul]

/-- Universal multiplicative lift: exact-additive, tensor-multiplicative object data descends
to a ring homomorphism from the exact Grothendieck ring.-/
noncomputable def ringLift {A : Type v} [CommRing A] (c : Object → A)
    (hadd : ∀ X Y Z, Exact X Y Z → c Y = c X + c Z)
    (hmul : ∀ X Y, c (T.tensor X Y) = c X * c Y)
    (hone : c T.unit = 1) :
    letI := T.commRing
    Group Object Exact →+* A := by
  letI := T.commRing
  exact {
    toFun := lift c hadd
    map_one' := lift_one T c hadd hone
    map_mul' := lift_product T c hadd hmul
    map_zero' := map_zero (lift c hadd)
    map_add' := map_add (lift c hadd) }

/-- The multiplicative universal lift has the prescribed value on every geometric object
class.-/
@[simp]
theorem ringLift_classOf {A : Type v} [CommRing A] (c : Object → A)
    (hadd : ∀ X Y Z, Exact X Y Z → c Y = c X + c Z)
    (hmul : ∀ X Y, c (T.tensor X Y) = c X * c Y)
    (hone : c T.unit = 1) (X : Object) :
    letI := T.commRing
    ringLift T c hadd hmul hone (classOf Object Exact X) = c X := by
  letI := T.commRing
  exact lift_classOf c hadd X

end CommutativeTensorData

end ExactGrothendieck
