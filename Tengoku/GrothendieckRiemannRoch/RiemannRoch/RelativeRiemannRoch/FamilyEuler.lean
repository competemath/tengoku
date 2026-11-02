/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.RelativeRiemannRoch.BaseChange

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Euler characteristics in a base-change-compatible family

The numerical Euler characteristic of a proper perfect family is the rank of its relative index
class. This file proves its compatibility with base change from two independent inputs: derived
base change for the index class and compatibility of the rank map on the bases.
-/

noncomputable section

universe u v w x

namespace RelativeRiemannRoch

variable {Total : Type u} {Total' : Type v} {Base : Type w} {Base' : Type x}
variable {ExactTotal : Total → Total → Total → Prop}
variable {ExactTotal' : Total' → Total' → Total' → Prop}
variable {ExactBase : Base → Base → Base → Prop}
variable {ExactBase' : Base' → Base' → Base' → Prop}

/-- Rank of the relative index class, i.e. the family Euler characteristic.-/
def familyEuler (push : Total → Base)
    (hpush : ∀ A B C, ExactTotal A B C → ExactBase (push A) (push B) (push C))
    (rank : ExactGrothendieck.Group Base ExactBase →+ ℤ) :
    ExactGrothendieck.Group Total ExactTotal →+ ℤ :=
  rank.comp (indexClass push hpush)

@[simp]
theorem familyEuler_classOf (push : Total → Base)
    (hpush : ∀ A B C, ExactTotal A B C → ExactBase (push A) (push B) (push C))
    (rank : ExactGrothendieck.Group Base ExactBase →+ ℤ) (E : Total) :
    familyEuler push hpush rank (ExactGrothendieck.classOf Total ExactTotal E) =
      rank (ExactGrothendieck.classOf Base ExactBase (push E)) := by
  simp [familyEuler, indexClass]

/-- Family Euler characteristics commute with a base change whenever the index square commutes
and the two rank maps are compatible.-/
theorem familyEuler_baseChange
    (push : Total → Base)
    (hpush : ∀ A B C, ExactTotal A B C → ExactBase (push A) (push B) (push C))
    (push' : Total' → Base')
    (hpush' : ∀ A B C,
      ExactTotal' A B C → ExactBase' (push' A) (push' B) (push' C))
    (pullTotal : Total → Total')
    (hpullTotal : ∀ A B C,
      ExactTotal A B C → ExactTotal' (pullTotal A) (pullTotal B) (pullTotal C))
    (pullBase : Base → Base')
    (hpullBase : ∀ A B C,
      ExactBase A B C → ExactBase' (pullBase A) (pullBase B) (pullBase C))
    (rank : ExactGrothendieck.Group Base ExactBase →+ ℤ)
    (rank' : ExactGrothendieck.Group Base' ExactBase' →+ ℤ)
    (hindex :
      (ExactGrothendieck.map pullBase hpullBase).comp (indexClass push hpush) =
        (indexClass push' hpush').comp (ExactGrothendieck.map pullTotal hpullTotal))
    (hrank : rank'.comp (ExactGrothendieck.map pullBase hpullBase) = rank) :
    familyEuler push hpush rank =
      (familyEuler push' hpush' rank').comp
        (ExactGrothendieck.map pullTotal hpullTotal) := by
  rw [← hrank]
  change (rank'.comp (ExactGrothendieck.map pullBase hpullBase)).comp
      (indexClass push hpush) =
    (rank'.comp (indexClass push' hpush')).comp
      (ExactGrothendieck.map pullTotal hpullTotal)
  rw [AddMonoidHom.comp_assoc, hindex]
  rfl

/-- Object-level derived base change and rank compatibility imply numerical base change directly.-/
theorem familyEuler_baseChange_of_object_classes
    (push : Total → Base)
    (hpush : ∀ A B C, ExactTotal A B C → ExactBase (push A) (push B) (push C))
    (push' : Total' → Base')
    (hpush' : ∀ A B C,
      ExactTotal' A B C → ExactBase' (push' A) (push' B) (push' C))
    (pullTotal : Total → Total')
    (hpullTotal : ∀ A B C,
      ExactTotal A B C → ExactTotal' (pullTotal A) (pullTotal B) (pullTotal C))
    (pullBase : Base → Base')
    (hpullBase : ∀ A B C,
      ExactBase A B C → ExactBase' (pullBase A) (pullBase B) (pullBase C))
    (rank : ExactGrothendieck.Group Base ExactBase →+ ℤ)
    (rank' : ExactGrothendieck.Group Base' ExactBase' →+ ℤ)
    (hobject : ∀ E : Total,
      ExactGrothendieck.classOf Base' ExactBase' (pullBase (push E)) =
        ExactGrothendieck.classOf Base' ExactBase' (push' (pullTotal E)))
    (hrank : rank'.comp (ExactGrothendieck.map pullBase hpullBase) = rank) :
    familyEuler push hpush rank =
      (familyEuler push' hpush' rank').comp
        (ExactGrothendieck.map pullTotal hpullTotal) :=
  familyEuler_baseChange push hpush push' hpush' pullTotal hpullTotal pullBase hpullBase rank rank'
    (baseChange_hom_eq_of_object_classes push hpush push' hpush' pullTotal hpullTotal
      pullBase hpullBase hobject) hrank

end RelativeRiemannRoch
