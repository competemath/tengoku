/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.GrothendieckRiemannRoch.DerivedComposition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Unconditional composition when the first factor is concentrated in degree zero

`derivedPushforward_comp_of_leray_euler` is gated on the bounded Euler equality `hleray` of a Leray
spectral sequence.  This file discharges that hypothesis in the one case where it is formal: when the
first higher-image system vanishes above degree zero.  Geometrically that is an **affine** morphism —
in particular a **closed immersion** — whose higher direct images vanish, so this is the closed
immersion half of milestone G4 of `docs/CONSTRUCTION_R5_GRR.md`, and it is strictly weaker than the
general spectral sequence exactly as that guide prescribes.

Contents:

* `concentratedHigherClass push`: `[push X]` in degree zero and `0` above it;
* `alternatingSum_concentratedHigherClass`: its alternating sum is `[push X]` — the whole content of
  the degeneration;
* `concentratedLongExactWitness`: the long exact witness, for every bound `n₁`, from
  exactness-preservation of `push` alone (the boundary family `w` is identically zero, so both
  endpoint conditions are `rfl`);
* `derivedPushforward_concentrated_eq_map`: the bounded derived pushforward of a degree-zero
  concentrated system **is** the naive functorial map `ExactGrothendieck.map push`.  This generalizes
  `derivedIdentity_eq_id`, which is the case `push = id`;
* `hleray_of_concentrated` and `derivedPushforward_comp_of_concentrated`: the Euler equality holds by
  construction, so the composition law becomes unconditional, with composite higher-image system
  `higher₂ ∘ push` and the *same* bound `n₂`.

Note the bound bookkeeping: the composite system reuses `n₂`, so the uniform-bound requirement of
`alternatingSum` (guide pitfall 3) is inherited from the second factor and nothing new has to be
chosen.  The first factor's bound `n₁` is arbitrary — a concentrated system satisfies the witness
conditions at every bound.
-/

set_option autoImplicit false

noncomputable section

universe u v w

namespace GrothendieckRiemannRoch

variable {Object : Type u} {Exact : Object → Object → Object → Prop}
variable {Object' : Type v} {Exact' : Object' → Object' → Object' → Prop}
variable {B : Type w} [AddCommGroup B]

/-- Higher-image classes of an object map that is concentrated in degree zero: the class of the
image in degree zero, and zero above it.-/
def concentratedHigherClass (push : Object → Object') (X : Object) (i : ℕ) :
    ExactGrothendieck.Group Object' Exact' :=
  if i = 0 then ExactGrothendieck.classOf Object' Exact' (push X) else 0

/-- The alternating sum of a degree-zero concentrated system is the image class.-/
theorem alternatingSum_concentratedHigherClass (push : Object → Object') (X : Object) (n₁ : ℕ) :
    alternatingSum n₁ (concentratedHigherClass (Exact' := Exact') push X) =
      ExactGrothendieck.classOf Object' Exact' (push X) := by
  rw [alternatingSum, Finset.sum_eq_single 0]
  · simp [concentratedHigherClass]
  · intro i _ hi
    simp [concentratedHigherClass, hi]
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.succ_pos n₁)) h

/-- The long exact witness of a degree-zero concentrated system, at any bound.  All boundary classes
are zero, so both endpoint conditions hold by `rfl`, and the middle decomposition is the defining
relation of the exact Grothendieck group applied to the image triple.-/
def concentratedLongExactWitness (n₁ : ℕ) (push : Object → Object')
    (hpush : ∀ X Y Z, Exact X Y Z → Exact' (push X) (push Y) (push Z))
    (X Y Z : Object) (h : Exact X Y Z) :
    LongExactWitness n₁ (concentratedHigherClass (Exact' := Exact') push X)
      (concentratedHigherClass (Exact' := Exact') push Y)
      (concentratedHigherClass (Exact' := Exact') push Z) where
  u i := if i = 0 then ExactGrothendieck.classOf Object' Exact' (push X) else 0
  v i := if i = 0 then ExactGrothendieck.classOf Object' Exact' (push Z) else 0
  w _ := 0
  leftBoundary := rfl
  rightBoundary := rfl
  leftDecomposition i := by
    by_cases hi : i = 0 <;> simp [concentratedHigherClass, hi]
  middleDecomposition i := by
    by_cases hi : i = 0
    · subst i
      simpa [concentratedHigherClass] using
        ExactGrothendieck.classOf_middle Object' Exact' (push X) (push Y) (push Z) (hpush X Y Z h)
    · simp [concentratedHigherClass, hi]
  rightDecomposition i := by
    by_cases hi : i = 0 <;> simp [concentratedHigherClass, hi]

/-- The bounded derived pushforward of a degree-zero concentrated system is the naive functorial
map.  Taking `push = id` recovers `derivedIdentity_eq_id`.-/
theorem derivedPushforward_concentrated_eq_map (n₁ : ℕ) (push : Object → Object')
    (hpush : ∀ X Y Z, Exact X Y Z → Exact' (push X) (push Y) (push Z)) :
    derivedPushforward n₁ (concentratedHigherClass (Exact' := Exact') push)
        (concentratedLongExactWitness n₁ push hpush) =
      ExactGrothendieck.map push hpush := by
  apply ExactGrothendieck.hom_ext Object Exact
  intro X
  rw [derivedPushforward_classOf, alternatingSum_concentratedHigherClass,
    ExactGrothendieck.map_classOf]

/-- **The bounded Euler equality is formal for a degree-zero concentrated first factor.**  This is
the `hleray` hypothesis of `derivedPushforward_comp_of_leray_euler`, discharged.-/
theorem hleray_of_concentrated (n₁ n₂ : ℕ) (push : Object → Object')
    (higher₂ : Object' → ℕ → B)
    (hlong₂ : ∀ X Y Z, Exact' X Y Z →
      LongExactWitness n₂ (higher₂ X) (higher₂ Y) (higher₂ Z))
    (X : Object) :
    derivedPushforward n₂ higher₂ hlong₂
        (alternatingSum n₁ (concentratedHigherClass (Exact' := Exact') push X)) =
      alternatingSum n₂ (fun i => higher₂ (push X) i) := by
  rw [alternatingSum_concentratedHigherClass, derivedPushforward_classOf]

/-- **Unconditional composition law for a degree-zero concentrated first factor.**  No Leray
spectral sequence is needed: the composite higher-image system is `higher₂ ∘ push` with the same
bound `n₂`.-/
theorem derivedPushforward_comp_of_concentrated (n₁ n₂ : ℕ) (push : Object → Object')
    (hpush : ∀ X Y Z, Exact X Y Z → Exact' (push X) (push Y) (push Z))
    (higher₂ : Object' → ℕ → B)
    (hlong₂ : ∀ X Y Z, Exact' X Y Z →
      LongExactWitness n₂ (higher₂ X) (higher₂ Y) (higher₂ Z)) :
    (derivedPushforward n₂ higher₂ hlong₂).comp
        (derivedPushforward n₁ (concentratedHigherClass (Exact' := Exact') push)
          (concentratedLongExactWitness n₁ push hpush)) =
      derivedPushforward n₂ (fun X i => higher₂ (push X) i)
        (fun X Y Z h => hlong₂ _ _ _ (hpush X Y Z h)) :=
  derivedPushforward_comp_of_leray_euler n₁ n₂ n₂
    (concentratedHigherClass (Exact' := Exact') push) higher₂
    (fun X i => higher₂ (push X) i)
    (concentratedLongExactWitness n₁ push hpush) hlong₂
    (fun X Y Z h => hlong₂ _ _ _ (hpush X Y Z h))
    (hleray_of_concentrated n₁ n₂ push higher₂ hlong₂)

/-- Pointwise form of the unconditional composition law.-/
theorem derivedPushforward_comp_apply_of_concentrated (n₁ n₂ : ℕ) (push : Object → Object')
    (hpush : ∀ X Y Z, Exact X Y Z → Exact' (push X) (push Y) (push Z))
    (higher₂ : Object' → ℕ → B)
    (hlong₂ : ∀ X Y Z, Exact' X Y Z →
      LongExactWitness n₂ (higher₂ X) (higher₂ Y) (higher₂ Z))
    (z : ExactGrothendieck.Group Object Exact) :
    derivedPushforward n₂ higher₂ hlong₂
        (derivedPushforward n₁ (concentratedHigherClass (Exact' := Exact') push)
          (concentratedLongExactWitness n₁ push hpush) z) =
      derivedPushforward n₂ (fun X i => higher₂ (push X) i)
        (fun X Y Z h => hlong₂ _ _ _ (hpush X Y Z h)) z :=
  congrArg (fun f : ExactGrothendieck.Group Object Exact →+ B ↦ f z)
    (derivedPushforward_comp_of_concentrated n₁ n₂ push hpush higher₂ hlong₂)

end GrothendieckRiemannRoch
