/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.Algebra.Algebra.Subalgebra.Tower
import Tengoku.Seed.RingTheory.IntegralClosure.Algebra.Basic
import Tengoku.Seed.RingTheory.Localization.Basic
import Tengoku.Seed.RingTheory.Localization.Away.Basic
import Tengoku.Seed.RingTheory.Localization.Integral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Recovering an algebra from its relative integral closure

If `T` is integral over a localization of R, its integral closure over R
recovers T after inverting the original denominators. This is an application
of Mathlib's integral-closure localization theorem, transported along the
literal bijective inclusion of the integral closure over the localized base.
The existing principal-localization API is the powers-submonoid specialization.
-/

noncomputable section

namespace SchemeTheory

universe u v w

/-- Recover an integral algebra over a localization from its actual relative
integral closure. The localization theorem and its transport are the existing
Mathlib constructions; the only extra comparison is the literal inclusion.
@isnad1 id=islocali.0h4v.s8.5b6f7c7dd2a0 from=translated src=- shape=e4f6f55c vocab=4282b6ce
-/
theorem integralClosure_isLocalization
    {R : Type u} [CommRing R] (M : Submonoid R)
    (A : Type v) [CommRing A] [Algebra R A] [IsLocalization M A]
    (T : Type w) [CommRing T] [Algebra R T] [Algebra A T]
    [IsScalarTower R A T] [Algebra.IsIntegral A T] :
    IsLocalization (Algebra.algebraMapSubmonoid (integralClosure R T) M) T := by
  let C := integralClosure R T
  let E := integralClosure A T
  have hunit : Algebra.algebraMapSubmonoid T M ≤ IsUnit.submonoid T := by
    rintro _ ⟨r, hr, rfl⟩
    change IsUnit (algebraMap R T r)
    rw [IsScalarTower.algebraMap_apply R A T]
    exact (IsLocalization.map_units A (⟨r, hr⟩ : M)).map (algebraMap A T)
  have : IsLocalization (Algebra.algebraMapSubmonoid T M) T :=
    IsLocalization.of_le_isUnit hunit
  let inclusion : C →ₐ[R] E := Subalgebra.inclusion
    (show integralClosure R T ≤ (integralClosure A T).restrictScalars R from
      fun x hx => (show IsIntegral R x from hx).tower_top)
  let : Algebra C E := inclusion.toRingHom.toAlgebra
  have : IsScalarTower R C E :=
    IsScalarTower.of_algebraMap_eq fun r => (inclusion.commutes r).symm
  have : IsScalarTower C E T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsLocalization (Algebra.algebraMapSubmonoid C M) E :=
    IsLocalization.integralClosure (R := R) (S := T) (Rf := A) (Sf := T) M
  let e : E ≃ₐ[C] T := AlgEquiv.ofBijective (IsScalarTower.toAlgHom C E T)
    ⟨fun x y h => Subtype.ext h,
      fun t => ⟨⟨t, Algebra.IsIntegral.isIntegral (R := A) t⟩, rfl⟩⟩
  exact IsLocalization.isLocalization_of_algEquiv (Algebra.algebraMapSubmonoid C M) e

/-- The relative integral closure in an integral `R[1/d]`-algebra has that
original algebra as its principal localization.
@isnad1 id=away.0h4v.s9.2137d422615f from=translated src=- shape=74c98786 vocab=347d2f5a
-/
theorem integralClosure_isLocalization_away
    {R : Type u} [CommRing R] (d : R)
    (A : Type v) [CommRing A] [Algebra R A] [IsLocalization.Away d A]
    (T : Type w) [CommRing T] [Algebra R T] [Algebra A T]
    [IsScalarTower R A T] [Algebra.IsIntegral A T] :
    IsLocalization.Away (algebraMap R (integralClosure R T) d) T := by
  simpa only [IsLocalization.Away, Algebra.algebraMapSubmonoid_powers] using
    integralClosure_isLocalization (Submonoid.powers d) A T

end SchemeTheory
