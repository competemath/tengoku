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

/-- The support used by `twoPointLaw` is nonempty.
@isnad1 id=nonempty.0h0v.s1.e40c00cad6cd from=translated src=- shape=25b03439 vocab=0d1fd298
-/
theorem twoPointSupport_nonempty : twoPointSupport.Nonempty := by
  simp [twoPointSupport]

/-- The uniform law on two points of a three-point ambient alphabet. -/
def twoPointLaw : PMF ThreePoint :=
  PMF.uniformOfFinset twoPointSupport twoPointSupport_nonempty

/-- The third ambient point is genuinely outside the support of `twoPointLaw`.
@isnad1 id=eq.0h0v.s3.1a0be274d944 from=translated src=- shape=390e0e93 vocab=7af2cc71
-/
@[simp]
theorem twoPointLaw_support :
    twoPointLaw.support = (twoPointSupport : Set ThreePoint) := by
  simp [twoPointLaw]

/--
For `twoPointLaw`, the support-cardinality entropy bound is strictly sharper
than the alphabet-cardinality bound.
@isnad1 id=and.0h0v.s5.61c7426ebbf5 from=translated src=- shape=2624a384 vocab=2c4bb348
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

/-- `supportEncoding` is not globally injective.
@isnad1 id=not.0h0v.s2.c904d8d3bfd2 from=translated src=- shape=6516253f vocab=3dfdd52f
-/
theorem supportEncoding_not_injective :
    Not (Function.Injective supportEncoding) := by
  intro h
  have heq : supportEncoding right = supportEncoding outside := rfl
  have := h heq
  cases this

/-- `supportEncoding` is injective where `twoPointLaw` carries mass.
@isnad1 id=injon.0h0v.s2.1b3593006eba from=translated src=- shape=437174ac vocab=d9e5ca41
-/
theorem supportEncoding_injOn_support :
    Set.InjOn supportEncoding twoPointLaw.support := by
  intro a ha b hb hab
  cases a <;> cases b <;>
    simp [twoPointLaw, twoPointSupport, supportEncoding] at ha hb hab ⊢

/-- Support-restricted injectivity is enough to preserve entropy.
@isnad1 id=eq.0h0v.s3.70102060d767 from=translated src=- shape=61caed72 vocab=0655092b
-/
theorem supportEncoding_preserves_entropy :
    entropyOf twoPointLaw supportEncoding = entropyOf twoPointLaw id := by
  exact
    (entropyOf_comp_eq_iff_injOn_support
      twoPointLaw id supportEncoding).2 (by
        simpa using supportEncoding_injOn_support)

/-- The first variable is a function of the second on the source support.
@isnad1 id=eq.0h0v.s4.782297fb6731 from=translated src=- shape=fde6cd3c vocab=04dc5179
-/
theorem functionalDependence_on_support :
    condEntropyOf twoPointLaw supportEncoding supportWitness = 0 := by
  apply
    (condEntropyOf_eq_zero_iff_exists_function
      twoPointLaw supportEncoding supportWitness).2
  refine ⟨id, ?_⟩
  intro omega homega
  cases omega <;>
    simp [twoPointLaw, twoPointSupport, supportEncoding, supportWitness] at homega ⊢

/-- The same functional relation fails at the unsupported ambient point.
@isnad1 id=ne.0h0v.s3.7d2d3d182301 from=translated src=- shape=366b9172 vocab=cc70c6a5
-/
theorem functionalDependence_not_global :
    supportEncoding outside ≠ id (supportWitness outside) := by
  decide

/-- A pure joint law with one positive and one null conditioning fiber. -/
def fiberLaw : PMF (Bool × Bool) := PMF.pure (false, false)

/-- A null conditioning fiber contributes numeric zero by convention.
@isnad1 id=and.0h0v.s5.23ba5908ce6b from=translated src=- shape=2fcad080 vocab=81197e85
-/
theorem nullFiber_zero :
    sndMarginal fiberLaw true = 0 ∧
      condEntropyFstGivenSnd fiberLaw true = 0 := by
  have hnull : sndMarginal fiberLaw true = 0 := by
    simp [fiberLaw, sndMarginal]
  exact
    ⟨hnull,
      condEntropyFstGivenSnd_of_sndMarginal_eq_zero fiberLaw hnull⟩

/-- The other conditioning fiber has positive mass.
@isnad1 id=ne.0h0v.s4.379c112f78eb from=translated src=- shape=75a4ecff vocab=c6d9fb34
-/
theorem positiveFiber_ne_zero : sndMarginal fiberLaw false ≠ 0 := by
  simp [fiberLaw, sndMarginal]

/-- On the positive fiber, zero entropy is equivalent to a pure conditional PMF.
@isnad1 id=iff.0h0v.s5.13949f4d80f1 from=translated src=- shape=cffd93ed vocab=04d048cd
-/
theorem positiveFiber_zero_iff_pure :
    condEntropyFstGivenSnd fiberLaw false = 0 ↔
      ∃ a, condFstGivenSnd fiberLaw false positiveFiber_ne_zero = PMF.pure a :=
  condEntropyFstGivenSnd_eq_zero_iff_of_sndMarginal_ne_zero
    fiberLaw positiveFiber_ne_zero

/-- The positive conditional fiber in `fiberLaw` is pure at `false`.
@isnad1 id=eq.0h0v.s3.350394b20efa from=translated src=- shape=32926e5b vocab=41de6211
-/
theorem positiveFiber_is_pure :
    condFstGivenSnd fiberLaw false positiveFiber_ne_zero = PMF.pure false := by
  have hmarginal : sndMarginal fiberLaw = PMF.pure false := by
    change (PMF.pure (false, false)).map Prod.snd = PMF.pure false
    rw [PMF.pure_map]
  apply PMF.ext
  intro a
  rw [condFstGivenSnd_apply, hmarginal]
  cases a <;> simp [fiberLaw]

/-- The positive fiber therefore has zero entropy for the substantive pure-law reason.
@isnad1 id=eq.0h0v.s3.eb816b4a6e56 from=translated src=- shape=c9f18549 vocab=f096ae1b
-/
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

/-- Without side information, `forgetSecond` does not preserve entropy.
@isnad1 id=ne.0h0v.s4.a899b2a27e37 from=translated src=- shape=c1bbe890 vocab=c07395fc
-/
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

/-- Side information restores the exact conditional-entropy equality contract.
@isnad1 id=eq.0h0v.s4.b0b930de9922 from=translated src=- shape=60ad71ad vocab=d6b92b85
-/
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
