/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.GrothendieckRiemannRoch.Pushforward

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The additive reduction step in Grothendieck--Riemann--Roch

This file constructs the two sides of GRR as independent additive maps. For an exact-preserving
object map `F`, the left side is `ch(F₊(-)) · td(Y)` and the right side is
`F₊(ch(-) · td(X))`. Equality on actual object classes then implies equality on every virtual
Grothendieck class.

No desired equality is stored in the data. A geometric GRR layer must separately construct the
Chern characters, Todd classes, cycle pushforward, and prove the formula on geometric generators.
-/

noncomputable section

universe u v w x

namespace GrothendieckRiemannRoch

variable {ObjectX : Type u} {ExactX : ObjectX → ObjectX → ObjectX → Prop}
variable {ObjectY : Type v} {ExactY : ObjectY → ObjectY → ObjectY → Prop}

/-- Multiplication by a fixed Todd class after an additive Chern character is additive.-/
def characteristicClass {C : Type w} [CommRing C]
    (chernCharacter : ExactGrothendieck.Group ObjectX ExactX →+ C) (toddClass : C) :
    ExactGrothendieck.Group ObjectX ExactX →+ C where
  toFun z := chernCharacter z * toddClass
  map_zero' := by simp
  map_add' a b := by rw [map_add, add_mul]

/--
@isnad1 id=eq.0h6v.s8.d7f1c138e882 from=translated src=- shape=85300a4f vocab=e8479896
-/
@[simp]
theorem characteristicClass_classOf {C : Type w} [CommRing C]
    (chernCharacter : ExactGrothendieck.Group ObjectX ExactX →+ C) (toddClass : C)
    (E : ObjectX) :
    characteristicClass chernCharacter toddClass
        (ExactGrothendieck.classOf ObjectX ExactX E) =
      chernCharacter (ExactGrothendieck.classOf ObjectX ExactX E) * toddClass :=
  rfl

/-- The left-hand side `ch(F₊(-)) · td(Y)` of GRR.-/
def leftHandSide {CY : Type w} [CommRing CY]
    (F : ObjectX → ObjectY)
    (hF : ∀ A B C, ExactX A B C → ExactY (F A) (F B) (F C))
    (chernY : ExactGrothendieck.Group ObjectY ExactY →+ CY) (toddY : CY) :
    ExactGrothendieck.Group ObjectX ExactX →+ CY :=
  (characteristicClass chernY toddY).comp (ExactGrothendieck.map F hF)

/-- The right-hand side `F₊(ch(-) · td(X))` of GRR.-/
def rightHandSide {CX : Type w} {CY : Type x} [CommRing CX] [CommRing CY]
    (chernX : ExactGrothendieck.Group ObjectX ExactX →+ CX) (toddX : CX)
    (cyclePushforward : CX →+ CY) :
    ExactGrothendieck.Group ObjectX ExactX →+ CY :=
  cyclePushforward.comp (characteristicClass chernX toddX)

/-- GRR on object classes implies equality of its two additive transformations on all of `K₀`
or `G₀`.
@isnad1 id=eq.1h13v.s9.35ad76845af5 from=translated src=- shape=658c6e8b vocab=424245fe
-/
theorem hom_eq_of_object_classes {CX : Type w} {CY : Type x} [CommRing CX] [CommRing CY]
    (F : ObjectX → ObjectY)
    (hF : ∀ A B C, ExactX A B C → ExactY (F A) (F B) (F C))
    (chernX : ExactGrothendieck.Group ObjectX ExactX →+ CX) (toddX : CX)
    (chernY : ExactGrothendieck.Group ObjectY ExactY →+ CY) (toddY : CY)
    (cyclePushforward : CX →+ CY)
    (hobject : ∀ E : ObjectX,
      chernY (ExactGrothendieck.classOf ObjectY ExactY (F E)) * toddY =
        cyclePushforward
          (chernX (ExactGrothendieck.classOf ObjectX ExactX E) * toddX)) :
    leftHandSide F hF chernY toddY =
      rightHandSide chernX toddX cyclePushforward := by
  apply ExactGrothendieck.hom_ext ObjectX ExactX
  intro E
  simpa [leftHandSide, rightHandSide] using hobject E

/-- Pointwise GRR for every virtual class, reduced to the formula on actual object classes.
@isnad1 id=eq.1h14v.s9.c5bd63887e61 from=translated src=- shape=8d6785ee vocab=f36bbdb5
-/
theorem formula_of_object_classes {CX : Type w} {CY : Type x} [CommRing CX] [CommRing CY]
    (F : ObjectX → ObjectY)
    (hF : ∀ A B C, ExactX A B C → ExactY (F A) (F B) (F C))
    (chernX : ExactGrothendieck.Group ObjectX ExactX →+ CX) (toddX : CX)
    (chernY : ExactGrothendieck.Group ObjectY ExactY →+ CY) (toddY : CY)
    (cyclePushforward : CX →+ CY)
    (hobject : ∀ E : ObjectX,
      chernY (ExactGrothendieck.classOf ObjectY ExactY (F E)) * toddY =
        cyclePushforward
          (chernX (ExactGrothendieck.classOf ObjectX ExactX E) * toddX))
    (z : ExactGrothendieck.Group ObjectX ExactX) :
    chernY (ExactGrothendieck.map F hF z) * toddY =
      cyclePushforward (chernX z * toddX) := by
  have h := congrArg (fun f : ExactGrothendieck.Group ObjectX ExactX →+ CY => f z)
    (hom_eq_of_object_classes F hF chernX toddX chernY toddY cyclePushforward hobject)
  exact h

end GrothendieckRiemannRoch
