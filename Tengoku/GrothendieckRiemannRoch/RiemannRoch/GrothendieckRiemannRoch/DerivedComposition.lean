/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.GrothendieckRiemannRoch.DerivedPushforward

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Identity and composition for bounded derived pushforwards

The identity functor has only a zeroth higher image, and its bounded-derived pushforward is the
identity on the exact Grothendieck group.  For two composable derived pushforwards, the Euler
equality supplied by a bounded Leray spectral sequence on actual object classes propagates to an
equality of homomorphisms on every virtual class.

The geometric layer remains responsible for constructing the spectral sequence and proving its
bounded Euler equality.  No functoriality is assumed at the virtual-class level.
-/

noncomputable section

universe u v w

namespace GrothendieckRiemannRoch

variable {Object : Type u} {Exact : Object → Object → Object → Prop}

/-- Higher-image classes for the identity: the object class in degree zero and zero thereafter.-/
def identityHigherClass (X : Object) (i : ℕ) : ExactGrothendieck.Group Object Exact :=
  if i = 0 then ExactGrothendieck.classOf Object Exact X else 0

/-- The degree-zero short-exact relation gives the long-exact witness for the identity functor.-/
def identityLongExactWitness (X Y Z : Object) (h : Exact X Y Z) :
    LongExactWitness 0 (identityHigherClass (Exact := Exact) X)
      (identityHigherClass (Exact := Exact) Y)
      (identityHigherClass (Exact := Exact) Z) where
  u i := if i = 0 then ExactGrothendieck.classOf Object Exact X else 0
  v i := if i = 0 then ExactGrothendieck.classOf Object Exact Z else 0
  w _ := 0
  leftBoundary := rfl
  rightBoundary := rfl
  leftDecomposition i := by
    by_cases hi : i = 0 <;> simp [identityHigherClass, hi]
  middleDecomposition i := by
    by_cases hi : i = 0
    · subst i
      simpa [identityHigherClass] using
        ExactGrothendieck.classOf_middle Object Exact X Y Z h
    · simp [identityHigherClass, hi]
  rightDecomposition i := by
    by_cases hi : i = 0 <;> simp [identityHigherClass, hi]

/-- The bounded-derived pushforward of the identity higher-image system.-/
def derivedIdentity :
    ExactGrothendieck.Group Object Exact →+ ExactGrothendieck.Group Object Exact :=
  derivedPushforward 0 (identityHigherClass (Exact := Exact)) identityLongExactWitness

/--
@isnad1 id=eq.0h3v.s7.87491c3970bd from=translated src=- shape=6fa2e584 vocab=9013fb2b
-/
@[simp]
theorem derivedIdentity_classOf (X : Object) :
    derivedIdentity (Object := Object) (Exact := Exact)
        (ExactGrothendieck.classOf Object Exact X) =
      ExactGrothendieck.classOf Object Exact X := by
  rw [derivedIdentity, derivedPushforward_classOf]
  simp [alternatingSum, identityHigherClass]

/-- The derived identity is the identity on every virtual class.
@isnad1 id=eq.0h2v.s6.5517cd7b3425 from=translated src=- shape=32722f08 vocab=fa2be2c7
-/
theorem derivedIdentity_eq_id :
    derivedIdentity (Object := Object) (Exact := Exact) =
      AddMonoidHom.id (ExactGrothendieck.Group Object Exact) := by
  apply ExactGrothendieck.hom_ext Object Exact
  intro X
  simp

variable {Object' : Type v} {Exact' : Object' → Object' → Object' → Prop}
variable {B : Type w} [AddCommGroup B]

/-- Composition law from the Euler equality of a bounded Leray spectral sequence on actual
objects.  The first higher-image system takes values in the intermediate exact Grothendieck
group; the second bounded derived pushforward acts on that entire virtual class.
@isnad1 id=eq.1h14v.s8.212729918db0 from=translated src=- shape=431349e2 vocab=ea568754
-/
theorem derivedPushforward_comp_of_leray_euler
    (n₁ n₂ n : ℕ)
    (higher₁ : Object → ℕ → ExactGrothendieck.Group Object' Exact')
    (higher₂ : Object' → ℕ → B)
    (higherComposite : Object → ℕ → B)
    (hlong₁ : ∀ X Y Z, Exact X Y Z →
      LongExactWitness n₁ (higher₁ X) (higher₁ Y) (higher₁ Z))
    (hlong₂ : ∀ X Y Z, Exact' X Y Z →
      LongExactWitness n₂ (higher₂ X) (higher₂ Y) (higher₂ Z))
    (hlongComposite : ∀ X Y Z, Exact X Y Z →
      LongExactWitness n (higherComposite X) (higherComposite Y) (higherComposite Z))
    (hleray : ∀ X,
      derivedPushforward n₂ higher₂ hlong₂ (alternatingSum n₁ (higher₁ X)) =
        alternatingSum n (higherComposite X)) :
    (derivedPushforward n₂ higher₂ hlong₂).comp
        (derivedPushforward n₁ higher₁ hlong₁) =
      derivedPushforward n higherComposite hlongComposite := by
  apply ExactGrothendieck.hom_ext Object Exact
  intro X
  simp only [AddMonoidHom.comp_apply, derivedPushforward_classOf]
  exact hleray X

/-- Pointwise form of the Leray--Euler composition theorem on every virtual class.
@isnad1 id=eq.1h15v.s9.75ee8c663558 from=translated src=- shape=e2eb745d vocab=de379c72
-/
theorem derivedPushforward_comp_apply_of_leray_euler
    (n₁ n₂ n : ℕ)
    (higher₁ : Object → ℕ → ExactGrothendieck.Group Object' Exact')
    (higher₂ : Object' → ℕ → B)
    (higherComposite : Object → ℕ → B)
    (hlong₁ : ∀ X Y Z, Exact X Y Z →
      LongExactWitness n₁ (higher₁ X) (higher₁ Y) (higher₁ Z))
    (hlong₂ : ∀ X Y Z, Exact' X Y Z →
      LongExactWitness n₂ (higher₂ X) (higher₂ Y) (higher₂ Z))
    (hlongComposite : ∀ X Y Z, Exact X Y Z →
      LongExactWitness n (higherComposite X) (higherComposite Y) (higherComposite Z))
    (hleray : ∀ X,
      derivedPushforward n₂ higher₂ hlong₂ (alternatingSum n₁ (higher₁ X)) =
        alternatingSum n (higherComposite X))
    (z : ExactGrothendieck.Group Object Exact) :
    derivedPushforward n₂ higher₂ hlong₂
        (derivedPushforward n₁ higher₁ hlong₁ z) =
      derivedPushforward n higherComposite hlongComposite z := by
  have h := congrArg
    (fun f : ExactGrothendieck.Group Object Exact →+ B ↦ f z)
    (derivedPushforward_comp_of_leray_euler n₁ n₂ n higher₁ higher₂
      higherComposite hlong₁ hlong₂ hlongComposite hleray)
  exact h

end GrothendieckRiemannRoch
