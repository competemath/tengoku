/-
Copyright © 2026 ECOLE POLYTECHNIQUE FEDERALE DE LAUSANNE (EPFL),
Switzerland, Mathematics of Information Laboratory (MIL).
All rights reserved.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

Author: Serhat Emre Coban
-/

import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.EntropyBounds
import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.SemanticBridge.Theorems

/-!
# Support-sensitive finite information examples

This opt-in module exercises the support-aware contracts in the finite Shannon
API. The examples distinguish ambient alphabets from PMF support, support-wise
from global functional dependence and injectivity, null from positive
conditioning fibers, and ordinary information loss from recovery using side
information.
-/

namespace LeanInfoTheory
namespace Examples
namespace SupportSensitive

open Shannon

noncomputable section

/-- A three-point ambient alphabet with one point omitted from the example law. -/
inductive ThreePoint where
  | left
  | right
  | outside
  deriving DecidableEq

instance ThreePoint.instFintype : Fintype ThreePoint where
  elems := {ThreePoint.left, ThreePoint.right, ThreePoint.outside}
  complete x := by
    cases x <;> simp

open ThreePoint

/-- The two atoms carrying mass in `twoPointLaw`. -/
def twoPointSupport : Finset ThreePoint := {left, right}

/-- The support used by `twoPointLaw` is nonempty. -/
theorem twoPointSupport_nonempty : twoPointSupport.Nonempty := by
  simp [twoPointSupport]

/-- The uniform law on two points of a three-point ambient alphabet. -/
def twoPointLaw : PMF ThreePoint :=
  PMF.uniformOfFinset twoPointSupport twoPointSupport_nonempty

/-- The third ambient point is genuinely outside the support of `twoPointLaw`. -/
@[simp]
theorem twoPointLaw_support :
    twoPointLaw.support = (twoPointSupport : Set ThreePoint) := by
  simp [twoPointLaw]

/--
For `twoPointLaw`, the support-cardinality entropy bound is strictly sharper
than the alphabet-cardinality bound.
-/
theorem supportBound_is_strictly_sharper :
    entropy twoPointLaw <= Real.log (twoPointLaw.support.ncard : Real) ∧
      Real.log (twoPointLaw.support.ncard : Real) <
        Real.log (Fintype.card ThreePoint : Real) := by
  refine ⟨entropy_le_log_support_ncard twoPointLaw, ?_⟩
  simp only [twoPointLaw_support]
  have hlog : Real.log (2 : Real) < Real.log (3 : Real) := by
    exact Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  have hcard : Fintype.card ThreePoint = 3 := by decide
  simpa [twoPointSupport, hcard] using hlog

/-- A map that separates the support but collides at an unsupported point. -/
def supportEncoding : ThreePoint -> Bool
  | left => false
  | right => true
  | outside => true

/-- A second map agreeing with `supportEncoding` only on `twoPointLaw.support`. -/
def supportWitness : ThreePoint -> Bool
  | left => false
  | right => true
  | outside => false

/-- `supportEncoding` is not globally injective. -/
theorem supportEncoding_not_injective :
    Not (Function.Injective supportEncoding) := by
  intro h
  have heq : supportEncoding right = supportEncoding outside := rfl
  have := h heq
  cases this

/-- `supportEncoding` is injective where `twoPointLaw` carries mass. -/
theorem supportEncoding_injOn_support :
    Set.InjOn supportEncoding twoPointLaw.support := by
  intro a ha b hb hab
  cases a <;> cases b <;>
    simp [twoPointLaw, twoPointSupport, supportEncoding] at ha hb hab ⊢

/-- Support-restricted injectivity is enough to preserve entropy. -/
theorem supportEncoding_preserves_entropy :
    entropyOf twoPointLaw supportEncoding = entropyOf twoPointLaw id := by
  exact
    (entropyOf_comp_eq_iff_injOn_support
      twoPointLaw id supportEncoding).2 (by
        simpa using supportEncoding_injOn_support)

/-- The first variable is a function of the second on the source support. -/
theorem functionalDependence_on_support :
    condEntropyOf twoPointLaw supportEncoding supportWitness = 0 := by
  apply
    (condEntropyOf_eq_zero_iff_exists_function
      twoPointLaw supportEncoding supportWitness).2
  refine ⟨id, ?_⟩
  intro omega homega
  cases omega <;>
    simp [twoPointLaw, twoPointSupport, supportEncoding, supportWitness] at homega ⊢

/-- The same functional relation fails at the unsupported ambient point. -/
theorem functionalDependence_not_global :
    supportEncoding outside ≠ id (supportWitness outside) := by
  decide

/-- A pure joint law with one positive and one null conditioning fiber. -/
def fiberLaw : PMF (Bool × Bool) := PMF.pure (false, false)

/-- A null conditioning fiber contributes numeric zero by convention. -/
theorem nullFiber_zero :
    sndMarginal fiberLaw true = 0 ∧
      condEntropyFstGivenSnd fiberLaw true = 0 := by
  have hnull : sndMarginal fiberLaw true = 0 := by
    simp [fiberLaw, sndMarginal]
  exact
    ⟨hnull,
      condEntropyFstGivenSnd_of_sndMarginal_eq_zero fiberLaw hnull⟩

/-- The other conditioning fiber has positive mass. -/
theorem positiveFiber_ne_zero : sndMarginal fiberLaw false ≠ 0 := by
  simp [fiberLaw, sndMarginal]

/-- On the positive fiber, zero entropy is equivalent to a pure conditional PMF. -/
theorem positiveFiber_zero_iff_pure :
    condEntropyFstGivenSnd fiberLaw false = 0 ↔
      ∃ a, condFstGivenSnd fiberLaw false positiveFiber_ne_zero = PMF.pure a :=
  condEntropyFstGivenSnd_eq_zero_iff_of_sndMarginal_ne_zero
    fiberLaw positiveFiber_ne_zero

/-- The positive conditional fiber in `fiberLaw` is pure at `false`. -/
theorem positiveFiber_is_pure :
    condFstGivenSnd fiberLaw false positiveFiber_ne_zero = PMF.pure false := by
  have hmarginal : sndMarginal fiberLaw = PMF.pure false := by
    change (PMF.pure (false, false)).map Prod.snd = PMF.pure false
    rw [PMF.pure_map]
  apply PMF.ext
  intro a
  rw [condFstGivenSnd_apply, hmarginal]
  cases a <;> simp [fiberLaw]

/-- The positive fiber therefore has zero entropy for the substantive pure-law reason. -/
theorem positiveFiber_zero : condEntropyFstGivenSnd fiberLaw false = 0 := by
  exact positiveFiber_zero_iff_pure.2 ⟨false, positiveFiber_is_pure⟩

/-- A full-support binary source for the side-information recovery example. -/
def recoveryLaw : PMF Bool := PMF.uniformOfFintype Bool

/-- The source variable whose second coordinate carries the random bit. -/
def recoveryX (omega : Bool) : Bool × Bool := (false, omega)

/-- Side information revealing the random bit. -/
def recoverySideInfo (omega : Bool) : Bool := omega

/-- Processing that discards the random second coordinate. -/
def forgetSecond : Bool × Bool -> Bool := Prod.fst

/-- A decoder that reconstructs `recoveryX` using the side information. -/
def recoverWithSideInfo (observation : Bool × Bool) : Bool × Bool :=
  (false, observation.2)

/-- Without side information, `forgetSecond` does not preserve entropy. -/
theorem forgetSecond_loses_entropy :
    entropyOf recoveryLaw (fun omega => forgetSecond (recoveryX omega)) ≠
      entropyOf recoveryLaw recoveryX := by
  intro heq
  have hinj :=
    (entropyOf_comp_eq_iff_injOn_support
      recoveryLaw recoveryX forgetSecond).1 heq
  have hfalse : recoveryX false ∈ (recoveryLaw.map recoveryX).support := by
    rw [PMF.support_map]
    exact ⟨false, by simp [recoveryLaw], rfl⟩
  have htrue : recoveryX true ∈ (recoveryLaw.map recoveryX).support := by
    rw [PMF.support_map]
    exact ⟨true, by simp [recoveryLaw], rfl⟩
  have hpair : recoveryX false = recoveryX true :=
    hinj hfalse htrue rfl
  have : false = true := congrArg Prod.snd hpair
  cases this

/-- Side information restores the exact conditional-entropy equality contract. -/
theorem sideInfo_preserves_condEntropy :
    condEntropyOf recoveryLaw
        (fun omega => forgetSecond (recoveryX omega)) recoverySideInfo =
      condEntropyOf recoveryLaw recoveryX recoverySideInfo := by
  apply
    (condEntropyOf_comp_eq_iff_exists_recovery
      recoveryLaw recoveryX recoverySideInfo forgetSecond).2
  refine ⟨recoverWithSideInfo, ?_⟩
  intro omega _homega
  cases omega <;> rfl

end

end SupportSensitive
end Examples
end LeanInfoTheory
