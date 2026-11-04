/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.KTheory.Presentation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The additive reduction step in Hirzebruch--Riemann--Roch

For an exact category, both sides of Hirzebruch--Riemann--Roch are additive in the coefficient
object. This file packages that statement without assuming the desired equality: the Euler
characteristic is induced from an independently supplied exact-additive integer invariant, while
the characteristic number is induced from an independently supplied Chern character, Todd class,
and integration map.

The main theorem says that equality on the classes of geometric objects implies equality on the
whole exact Grothendieck group. Constructing the geometric Chern character, Todd class, and
integration map remains a separate geometric layer.
-/

noncomputable section

universe u v

namespace HirzebruchRiemannRoch

variable {Object : Type u} {Exact : Object → Object → Object → Prop}

/-- The rational Euler-characteristic homomorphism induced by an exact-additive integer-valued
invariant on objects.-/
def eulerHom (euler : Object → ℤ)
    (hadd : ∀ A B C, Exact A B C → euler B = euler A + euler C) :
    ExactGrothendieck.Group Object Exact →+ ℚ :=
  (Int.castAddHom ℚ).comp (ExactGrothendieck.lift euler hadd)

/--
@isnad1 id=eq.1h4v.s7.8e6d492cbea3 from=translated src=- shape=60f90bc5 vocab=df3c7811
-/
@[simp]
theorem eulerHom_classOf (euler : Object → ℤ)
    (hadd : ∀ A B C, Exact A B C → euler B = euler A + euler C) (E : Object) :
    eulerHom euler hadd (ExactGrothendieck.classOf Object Exact E) = euler E := by
  simp [eulerHom, ExactGrothendieck.lift_classOf]

variable {A : Type v} [CommRing A]

/-- The HRR characteristic number `∫ ch(-) · td`, regarded as an additive homomorphism on the
Grothendieck group. The inputs are deliberately independent of the Euler characteristic.-/
def characteristicNumber
    (chernCharacter : ExactGrothendieck.Group Object Exact →+ A)
    (toddClass : A) (integral : A →+ ℚ) :
    ExactGrothendieck.Group Object Exact →+ ℚ where
  toFun x := integral (chernCharacter x * toddClass)
  map_zero' := by simp
  map_add' x y := by
    rw [map_add, add_mul, map_add]

/--
@isnad1 id=eq.0h7v.s8.d61ded0487ed from=translated src=- shape=4253920b vocab=711e82d6
-/
@[simp]
theorem characteristicNumber_classOf
    (chernCharacter : ExactGrothendieck.Group Object Exact →+ A)
    (toddClass : A) (integral : A →+ ℚ) (E : Object) :
    characteristicNumber chernCharacter toddClass integral
        (ExactGrothendieck.classOf Object Exact E) =
      integral (chernCharacter (ExactGrothendieck.classOf Object Exact E) * toddClass) :=
  rfl

/-- The exact-additivity reduction for Hirzebruch--Riemann--Roch: it is enough to verify the
formula on object classes, because those classes generate the exact Grothendieck group.
@isnad1 id=eq.2h7v.s8.2ece7073cb69 from=translated src=- shape=4a117354 vocab=14a04a74
-/
theorem hom_eq_of_object_classes
    (euler : Object → ℤ)
    (euler_additive : ∀ A B C, Exact A B C → euler B = euler A + euler C)
    (chernCharacter : ExactGrothendieck.Group Object Exact →+ A)
    (toddClass : A) (integral : A →+ ℚ)
    (hobject : ∀ E : Object,
      (euler E : ℚ) =
        integral (chernCharacter (ExactGrothendieck.classOf Object Exact E) * toddClass)) :
    eulerHom euler euler_additive =
      characteristicNumber chernCharacter toddClass integral := by
  apply ExactGrothendieck.hom_ext Object Exact
  intro E
  rw [eulerHom_classOf, characteristicNumber_classOf]
  exact hobject E

/-- Pointwise HRR on every virtual class, deduced from the formula on actual object classes.
@isnad1 id=eq.2h8v.s9.79ee2470752c from=translated src=- shape=36be9c74 vocab=79772f96
-/
theorem formula_of_object_classes
    (euler : Object → ℤ)
    (euler_additive : ∀ A B C, Exact A B C → euler B = euler A + euler C)
    (chernCharacter : ExactGrothendieck.Group Object Exact →+ A)
    (toddClass : A) (integral : A →+ ℚ)
    (hobject : ∀ E : Object,
      (euler E : ℚ) =
        integral (chernCharacter (ExactGrothendieck.classOf Object Exact E) * toddClass))
    (x : ExactGrothendieck.Group Object Exact) :
    eulerHom euler euler_additive x =
      integral (chernCharacter x * toddClass) := by
  have h := congrArg (fun f : ExactGrothendieck.Group Object Exact →+ ℚ => f x)
    (hom_eq_of_object_classes euler euler_additive chernCharacter toddClass integral hobject)
  exact h

end HirzebruchRiemannRoch
