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

/--
@isnad1 id=eq.0h6v.s7.a4f7e7f368f8 from=translated src=- shape=901924a1 vocab=cfa31ff2
-/
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

/--
@isnad1 id=eq.0h7v.s8.1cda3766421f from=translated src=- shape=64f58312 vocab=6a64d75d
-/
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

/--
@isnad1 id=eq.0h7v.s6.bbbc9b18cb2f from=translated src=- shape=91c742cc vocab=3b4a9d0b
-/
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

/--
@isnad1 id=eq.0h8v.s7.dd674758cebe from=translated src=- shape=167a4a26 vocab=87d4e303
-/
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

/--
@isnad1 id=eq.0h8v.s7.acdbbddcb30b from=translated src=- shape=662956f2 vocab=87d4e303
-/
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

/--
@isnad1 id=eq.0h6v.s7.a24fd3e932d3 from=translated src=- shape=5699a49b vocab=6e36ec03
-/
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

/--
@isnad1 id=eq.0h6v.s7.171e36d0e34a from=translated src=- shape=e367c45b vocab=6e36ec03
-/
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

/--
@isnad1 id=eq.0h7v.s8.00265cd5ff7c from=translated src=- shape=4af2d606 vocab=02a2a918
-/
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

/--
@isnad1 id=eq.0h7v.s10.8b79d73f1867 from=translated src=- shape=d444bb74 vocab=3db839f5
-/
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

/-- Associativity on object classes propagates to associativity on every virtual class.
@isnad1 id=eq.1h8v.s7.135353a04e75 from=translated src=- shape=18670442 vocab=3b4a9d0b
-/
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

/-- Commutativity on object classes propagates to commutativity on every virtual class.
@isnad1 id=eq.1h7v.s6.6dfa50416981 from=translated src=- shape=8bf92884 vocab=3b4a9d0b
-/
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

/-- A left-unit law on object classes propagates to every virtual class.
@isnad1 id=eq.1h7v.s6.edc03c53d12a from=translated src=- shape=50a74594 vocab=3b4a9d0b
-/
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

/-- A right-unit law on object classes propagates to every virtual class.
@isnad1 id=eq.1h7v.s6.289831022f4a from=translated src=- shape=e8e82fc3 vocab=3b4a9d0b
-/
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

/-- The multiplication field of `commRing` is the independently constructed quotient product.
@isnad1 id=eq.0h5v.s5.86a83721b59c from=translated src=- shape=008fffd3 vocab=02ebb9c0
-/
theorem commRing_mul_eq (x y : Group Object Exact) :
    @Mul.mul (Group Object Exact) T.commRing.toMul x y = T.mul x y :=
  rfl

/-- The unit field of `commRing` is the class of the geometric tensor unit.
@isnad1 id=eq.0h3v.s5.13a9e6f4d469 from=translated src=- shape=d57042b8 vocab=5ce3d599
-/
theorem commRing_one_eq :
    @OfNat.ofNat (Group Object Exact) 1 T.commRing.toOfNat1 = T.one :=
  rfl

/-- An exact-additive object invariant which is multiplicative on tensor products is
multiplicative on all virtual classes.
@isnad1 id=eq.2h7v.s8.655b683cd79d from=translated src=- shape=f5460d21 vocab=8f218510
-/
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
unit to one.
@isnad1 id=eq.2h5v.s7.275c7a392038 from=translated src=- shape=a9dc1791 vocab=2fa13223
-/
theorem lift_one {A : Type v} [CommRing A] (c : Object → A)
    (hadd : ∀ X Y Z, Exact X Y Z → c Y = c X + c Z)
    (hone : c T.unit = 1) : lift c hadd T.one = 1 := by
  change lift c hadd (classOf Object Exact T.unit) = 1
  rw [lift_classOf]
  exact hone

/-- Left unit law for every virtual class.
@isnad1 id=eq.0h4v.s5.18b21d3cb388 from=translated src=- shape=31092601 vocab=8e94c038
-/
theorem one_mul (x : Group Object Exact) : T.mul T.one x = x :=
  product_one_left_of_classOf T.tensor T.exactLeft T.exactRight T.unit T.unitClass x

/-- Right unit law for every virtual class, obtained from the left unit by commutativity on
object classes.
@isnad1 id=eq.0h4v.s5.c8ccd301a265 from=translated src=- shape=cd915229 vocab=8e94c038
-/
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
class.
@isnad1 id=eq.3h6v.s7.321ed2599f84 from=translated src=- shape=536458e6 vocab=a968d834
-/
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
