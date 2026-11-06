/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.IntegralClosure
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianValuationExtension
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Defectless
import Tengoku.Seed.RingTheory.RamificationInertia.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite valued extension consequences

This file collects theorem-level consequences around finite valued extensions:
canonical local-Dedekind degree formulas, uniqueness criteria for extended
valuations, and the algebra equivalence identifying an actual integral-closure
valuation ring with mathlib's `integralClosure`.
-/

namespace ValuationTheory

noncomputable section

universe u v w x y

namespace DiscreteValuationField
namespace ValuedExtension

open ValuationTheory.DiscreteValuationField.Valuation

/-- If an element maps into the maximal ideal of a local target ring, then the
original element is in the maximal ideal of the local source ring.  This is the
automatic half of the center/maximal-ideal condition used in the Henselian
finite-extension frontier.
@isnad1 id=mem.1h4v.s7.100e498672b4 from=translated src=- shape=f515355e vocab=b5a6906e
-/
theorem mem_maximalIdeal_of_map_mem_maximalIdeal
    {R : Type u} {S : Type w} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (f : R →+* S) {x : R}
    (hx : f x ∈ IsLocalRing.maximalIdeal S) :
    x ∈ IsLocalRing.maximalIdeal R := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  intro hxunit
  exact hx (hxunit.map f)

/-- Integral valuation overrings have maximal center.

For a valuation overring `R ≤ S`, if the inclusion is integral, then the center
of `S` on `R` is the maximal ideal of `R`.  This is the usable form needed in
the Henselian finite-extension frontier, where the remaining mathematical work
is to prove integrality of the relevant extension valuation-ring inclusions.
@isnad1 id=eq.2h3v.s7.20a2c060d975 from=translated src=- shape=a5fcd168 vocab=54e9a2ac
-/
theorem idealOfLE_eq_maximalIdeal_of_isIntegral
    {M : Type u} [Field M] (R S : ValuationSubring M) (hRS : R ≤ S)
    (hIntegral : (R.inclusion S hRS).IsIntegral) :
    ValuationSubring.idealOfLE R S hRS = IsLocalRing.maximalIdeal R := by
  exact ((IsLocalRing.local_hom_TFAE (R.inclusion S hRS)).out 1 5).mp
    (hIntegral.isLocalHom (by
      intro x y hxy
      apply Subtype.ext
      calc
        (x : M) = ((R.inclusion S hRS x : S) : M) := rfl
        _ = ((R.inclusion S hRS y : S) : M) := congrArg Subtype.val hxy
        _ = (y : M) := rfl))

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- The canonical integer map from the base valuation ring to the valuation
subring constructed from the actual integral closure.  Its definition uses the
exact pullback theorem for the constructed integral-closure valuation subring,
so no auxiliary alias of the base or target valuation ring is introduced.-/
def integralClosureValuationSubringIntegerMapOfMemOrInv
    (base : CompleteDVF.{u, v} K)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring) :
    base.valuationSubring →+*
      integralClosureValuationSubringOfMemOrInv
        (L := L) base.valuation hval where
  toFun a :=
    ⟨algebraMap K L (a : K),
      (integralClosureValuationSubringOfMemOrInv_pullback
        (L := L) base.valuation hval (a : K)).2 a.2⟩
  map_zero' := Subtype.ext (map_zero (algebraMap K L))
  map_one' := Subtype.ext (map_one (algebraMap K L))
  map_add' := fun a b => Subtype.ext (map_add (algebraMap K L) (a : K) (b : K))
  map_mul' := fun a b => Subtype.ext (map_mul (algebraMap K L) (a : K) (b : K))

omit [FiniteDimensional K L] in
/-- The finite-extension integer map into the integral closure is the ambient algebra map.
@isnad1 id=eq.1h4v.s10.b5b04e965c28 from=translated src=- shape=75fef3b9 vocab=e327cae1
-/
@[simp] theorem integralClosureValuationSubringIntegerMapOfMemOrInv_apply
    (base : CompleteDVF.{u, v} K)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (a : base.valuationSubring) :
    ((integralClosureValuationSubringIntegerMapOfMemOrInv
      (K := K) (L := L) base hval a :
        integralClosureValuationSubringOfMemOrInv
          (L := L) base.valuation hval) : L) =
      algebraMap K L (a : K) :=
  rfl

omit [FiniteDimensional K L] in
/-- The canonical integer map into the valuation subring built from the actual
integral closure is injective.  This is the ring-theoretic input needed to
turn a prime over the base maximal ideal into a nonzero prime of the constructed
integral-closure valuation ring.
@isnad1 id=injectiv.1h3v.s10.a3d8004ed7be from=translated src=- shape=a8a50c17 vocab=39ac8378
-/
theorem integralClosureValuationSubringIntegerMapOfMemOrInv_injective
    (base : CompleteDVF.{u, v} K)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring) :
    Function.Injective
      (integralClosureValuationSubringIntegerMapOfMemOrInv
        (K := K) (L := L) base hval) := by
  intro a b hab
  apply Subtype.ext
  apply FaithfulSMul.algebraMap_injective K L
  have hvalEq := congrArg
    (fun x :
      integralClosureValuationSubringOfMemOrInv
        (L := L) base.valuation hval => (x : L)) hab
  change algebraMap K L (a : K) = algebraMap K L (b : K) at hvalEq
  exact hvalEq

/- Numerical defect is a derived quotient; defectlessness itself is the
canonical equality `degree = e * f` defined in `Extensions`.  Positivity
and the fundamental identity are established below only under the hypotheses
needed by the local-Dedekind theorem. -/

omit [FiniteDimensional K L] in
/-- The center of an extension valuation ring on the constructed actual
integral-closure valuation subring contracts to the base maximal ideal.

This is the nontrivial half of locating the center: the center is represented
as `ValuationSubring.idealOfLE`, and its contraction along the canonical map
from the base valuation ring is computed using the `HasExtension` valuation
inequality.  A later Henselian local-integral-closure theorem can combine this
with uniqueness of primes above the base maximal ideal to identify the center
with the maximal ideal of the constructed integral closure.
@isnad1 id=other.1h5v.s10.13cd9adb544c from=translated src=- shape=2198cb8b vocab=901db14c
-/
theorem idealOfLE_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (base : CompleteDVF.{u, v} K) (vL : _root_.Valuation L ΓL)
    [base.valuation.HasExtension vL]
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring) :
    let B :=
      integralClosureValuationSubringOfMemOrInv
        (L := L) base.valuation hval
    let hvL_le : B ≤ vL.valuationSubring :=
      integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
        (L := L) base.valuation vL hval
    (ValuationSubring.idealOfLE B vL.valuationSubring hvL_le).comap
        (integralClosureValuationSubringIntegerMapOfMemOrInv
          (K := K) (L := L) base hval) =
      base.maximalIdeal := by
  let B :=
    integralClosureValuationSubringOfMemOrInv
      (L := L) base.valuation hval
  let hvL_le : B ≤ vL.valuationSubring :=
    integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
      (L := L) base.valuation vL hval
  let i : base.valuationSubring →+* B :=
    integralClosureValuationSubringIntegerMapOfMemOrInv
      (K := K) (L := L) base hval
  apply Ideal.ext
  intro a
  rw [Ideal.mem_comap]
  change B.inclusion vL.valuationSubring hvL_le (i a) ∈
      IsLocalRing.maximalIdeal vL.valuationSubring ↔
    a ∈ IsLocalRing.maximalIdeal base.valuation.valuationSubring
  rw [Valuation.mem_maximalIdeal_iff (v := vL)]
  rw [Valuation.mem_maximalIdeal_iff (v := base.valuation)]
  change vL
      ((B.inclusion vL.valuationSubring hvL_le (i a) :
        vL.valuationSubring) : L) < 1 ↔
    base.valuation (a : K) < 1
  have hcoe :
      ((B.inclusion vL.valuationSubring hvL_le (i a) :
        vL.valuationSubring) : L) =
        algebraMap K L (a : K) := by
    rfl
  rw [hcoe]
  exact Valuation.HasExtension.val_map_lt_one_iff base.valuation vL (a : K)

/-- In a finite separable extension, once the actual integral closure has the
valuation-ring dichotomy, the constructed integral-closure valuation ring has a
unique prime over the base maximal ideal.

The proof uses real structure, not a certificate: the constructed valuation
ring is the actual integral closure, hence Dedekind over the base DVR; a prime
whose contraction is the base maximal ideal is nonzero by injectivity of the
canonical integer map, hence maximal by the dimension-one property, and then
equal to the unique maximal ideal because the constructed ring is local.
@isnad1 id=eq.3h4v.s10.9db77c1a985e from=translated src=- shape=53c85295 vocab=96d23a64
-/
theorem prime_eq_maximalIdeal_of_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal
    (base : CompleteDVF.{u, v} K)
    [Algebra.IsSeparable K L]
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (P :
      Ideal
        (integralClosureValuationSubringOfMemOrInv
          (L := L) base.valuation hval))
    (hP : P.IsPrime)
    (hcomap :
      P.comap
          (integralClosureValuationSubringIntegerMapOfMemOrInv
            (K := K) (L := L) base hval) =
        base.maximalIdeal) :
    P =
      IsLocalRing.maximalIdeal
        (integralClosureValuationSubringOfMemOrInv
          (L := L) base.valuation hval) := by
  let B :=
    integralClosureValuationSubringOfMemOrInv
      (L := L) base.valuation hval
  let i : base.valuationSubring →+* B :=
    integralClosureValuationSubringIntegerMapOfMemOrInv
      (K := K) (L := L) base hval
  let : base.valuation.HasExtension B.valuation :=
    integralClosureValuationSubringOfMemOrInv_hasExtension
      (L := L) base.valuation hval
  let : IsFractionRing base.valuationSubring K :=
    base_valuationSubring_isFractionRing (K := K) base
  let : IsDiscreteValuationRing base.valuationSubring :=
    base.valuationSubring_isDiscreteValuationRing
  let : IsDedekindDomain base.valuationSubring := inferInstance
  let : Algebra base.valuationSubring B := RingHom.toAlgebra i
  let : IsScalarTower base.valuationSubring B L :=
    IsScalarTower.of_algebraMap_eq (by
      intro a
      rfl)
  let : IsIntegralClosure B base.valuationSubring L :=
    integralClosureValuationSubringOfMemOrInv_isIntegralClosure
      (L := L) base.valuation hval
  let : IsDedekindDomain B :=
    IsIntegralClosure.isDedekindDomain base.valuationSubring K L B
  have hi : Function.Injective i :=
    integralClosureValuationSubringIntegerMapOfMemOrInv_injective
      (K := K) (L := L) base hval
  have hP_ne_bot : P ≠ ⊥ := by
    have hnot_le_bot : ¬ base.maximalIdeal ≤ ⊥ := by
      intro hle
      exact base.maximalIdeal_ne_bot (le_antisymm hle bot_le)
    obtain ⟨a, ha_max, ha_not_bot⟩ := Set.not_subset.mp hnot_le_bot
    have ha_ne_zero : a ≠ 0 := by
      intro ha
      exact ha_not_bot (by simp [ha])
    intro hPbot
    have ha_comap : a ∈ P.comap i := by
      simpa [B, i, hcomap] using ha_max
    have hai_mem : i a ∈ P := by
      simpa [Ideal.mem_comap] using ha_comap
    have hai_zero : i a = 0 := by
      simpa [hPbot] using hai_mem
    exact ha_ne_zero (hi (by simpa using hai_zero))
  exact IsLocalRing.eq_maximalIdeal (hP.isMaximal hP_ne_bot)

end ValuedExtension
end DiscreteValuationField

end

end ValuationTheory
