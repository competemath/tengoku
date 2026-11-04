/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.GrothendieckRiemannRoch.Pushforward

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Base change for relative index classes

For a cartesian family square, derived base change is first a statement on actual coefficient
objects. Once the four operations preserve exact triples, that statement extends canonically to
all virtual classes. This file proves that extension and makes every required hypothesis explicit.

The geometric layer must instantiate the object types by perfect complexes or coherent complexes,
and supply the derived base-change theorem under its properness, Tor-independence, and finiteness
hypotheses. No unrestricted base-change assertion is made here.
-/

noncomputable section

universe u v w x

namespace RelativeRiemannRoch

variable {Total : Type u} {Total' : Type v} {Base : Type w} {Base' : Type x}
variable {ExactTotal : Total → Total → Total → Prop}
variable {ExactTotal' : Total' → Total' → Total' → Prop}
variable {ExactBase : Base → Base → Base → Prop}
variable {ExactBase' : Base' → Base' → Base' → Prop}

/-- The relative index class `f₊[E]` in the Grothendieck group of the base.-/
def indexClass (push : Total → Base)
    (hpush : ∀ A B C, ExactTotal A B C → ExactBase (push A) (push B) (push C)) :
    ExactGrothendieck.Group Total ExactTotal →+
      ExactGrothendieck.Group Base ExactBase :=
  ExactGrothendieck.map push hpush

/--
@isnad1 id=eq.0h7v.s7.9f549c929c89 from=translated src=- shape=104a555d vocab=a4234738
-/
@[simp]
theorem indexClass_classOf (push : Total → Base)
    (hpush : ∀ A B C, ExactTotal A B C → ExactBase (push A) (push B) (push C))
    (E : Total) :
    indexClass push hpush (ExactGrothendieck.classOf Total ExactTotal E) =
      ExactGrothendieck.classOf Base ExactBase (push E) := by
  simp [indexClass]

/-- Derived base change on actual object classes extends to a commuting square on exact
Grothendieck groups.
@isnad1 id=eq.1h16v.s8.94bb29fc8f6d from=translated src=- shape=8cc11550 vocab=2850b3a9
-/
theorem baseChange_hom_eq_of_object_classes
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
    (hobject : ∀ E : Total,
      ExactGrothendieck.classOf Base' ExactBase' (pullBase (push E)) =
        ExactGrothendieck.classOf Base' ExactBase' (push' (pullTotal E))) :
    (ExactGrothendieck.map pullBase hpullBase).comp (indexClass push hpush) =
      (indexClass push' hpush').comp (ExactGrothendieck.map pullTotal hpullTotal) := by
  apply ExactGrothendieck.hom_ext Total ExactTotal
  intro E
  simpa [indexClass] using hobject E

/-- Pointwise base change for every virtual coefficient class.
@isnad1 id=eq.1h17v.s9.38bff01eaff1 from=translated src=- shape=43e4d46d vocab=ccbc2c97
-/
theorem baseChange_indexClass_of_object_classes
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
    (hobject : ∀ E : Total,
      ExactGrothendieck.classOf Base' ExactBase' (pullBase (push E)) =
        ExactGrothendieck.classOf Base' ExactBase' (push' (pullTotal E)))
    (z : ExactGrothendieck.Group Total ExactTotal) :
    ExactGrothendieck.map pullBase hpullBase (indexClass push hpush z) =
      indexClass push' hpush' (ExactGrothendieck.map pullTotal hpullTotal z) := by
  have h := congrArg
    (fun f : ExactGrothendieck.Group Total ExactTotal →+
        ExactGrothendieck.Group Base' ExactBase' => f z)
    (baseChange_hom_eq_of_object_classes push hpush push' hpush' pullTotal hpullTotal
      pullBase hpullBase hobject)
  exact h

end RelativeRiemannRoch
