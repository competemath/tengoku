/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Degree
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Uniqueness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Uniqueness criteria for extensions of Henselian discrete valuations

The integral closure of the base valuation ring supplies the valuation subring
used to compare extensions. Local maximal-ideal centers and subsingleton fibers
lead to uniqueness criteria, including criteria obtained from Henselian quotient
maps, adic completeness, and finite-separable extensions.
-/

namespace ValuationTheory

noncomputable section

universe u v w x y

namespace DiscreteValuationField

namespace ValuedExtension.Henselian

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]
variable (base : HenselianDVF.{u, v} K) (target : HenselianDVF.{w, x} L)
variable [base.toDVF.valuation.HasExtension target.toDVF.valuation]

/-- The canonical integer map from a Henselian base valuation ring to the
valuation subring constructed from the actual integral closure.-/
def integralClosureValuationSubringIntegerMapOfMemOrInv
    (base : HenselianDVF.{u, v} K)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring) :
    base.valuationSubring →+*
      ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
        (L := L) base.toDVF.valuation hval where
  toFun a :=
    ⟨algebraMap K L (a : K),
      (Valuation.integralClosureValuationSubringOfMemOrInv_pullback
        (L := L) base.toDVF.valuation hval (a : K)).2 a.2⟩
  map_zero' := Subtype.ext (map_zero (algebraMap K L))
  map_one' := Subtype.ext (map_one (algebraMap K L))
  map_add' := fun a b => Subtype.ext (map_add (algebraMap K L) (a : K) (b : K))
  map_mul' := fun a b => Subtype.ext (map_mul (algebraMap K L) (a : K) (b : K))

omit [FiniteDimensional K L] in
/-- The integer map into the integral-closure valuation ring is the ambient algebra map.
@isnad1 id=eq.1h4v.s10.0d0117ad2b79 from=translated src=- shape=6b083769 vocab=d5a724de
-/
@[simp] theorem integralClosureValuationSubringIntegerMapOfMemOrInv_apply
    (base : HenselianDVF.{u, v} K)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (a : base.valuationSubring) :
    ((integralClosureValuationSubringIntegerMapOfMemOrInv
      (K := K) (L := L) base hval a :
        ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
          (L := L) base.toDVF.valuation hval) : L) =
      algebraMap K L (a : K) :=
  rfl

omit [FiniteDimensional K L] in
/-- The canonical integer map into the valuation subring built from the actual
integral closure is injective.
@isnad1 id=injectiv.1h3v.s9.83d75a0ec7a9 from=translated src=- shape=02275044 vocab=e32fb441
-/
theorem integralClosureValuationSubringIntegerMapOfMemOrInv_injective
    (base : HenselianDVF.{u, v} K)
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
  simpa using
    congrArg
      (fun x :
        ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
          (L := L) base.toDVF.valuation hval => (x : L)) hab

omit [FiniteDimensional K L] in
/-- The center of an extension valuation ring on the constructed actual
integral-closure valuation subring contracts to the base maximal ideal.
@isnad1 id=other.1h5v.s10.00f2c20153bd from=translated src=- shape=0a4e7eb5 vocab=8e6d3640
-/
theorem idealOfLE_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (base : HenselianDVF.{u, v} K) (vL : _root_.Valuation L ΓL)
    [base.toDVF.valuation.HasExtension vL]
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring) :
    let B :=
      ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
        (L := L) base.toDVF.valuation hval
    let hvL_le : B ≤ vL.valuationSubring :=
      Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
        (L := L) base.toDVF.valuation vL hval
    (ValuationSubring.idealOfLE B vL.valuationSubring hvL_le).comap
        (integralClosureValuationSubringIntegerMapOfMemOrInv
          (K := K) (L := L) base hval) =
      base.maximalIdeal := by
  let B :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
      (L := L) base.toDVF.valuation hval
  let hvL_le : B ≤ vL.valuationSubring :=
    Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
      (L := L) base.toDVF.valuation vL hval
  let i : base.valuationSubring →+* B :=
    integralClosureValuationSubringIntegerMapOfMemOrInv
      (K := K) (L := L) base hval
  apply Ideal.ext
  intro a
  rw [Ideal.mem_comap]
  change B.inclusion vL.valuationSubring hvL_le (i a) ∈
      IsLocalRing.maximalIdeal vL.valuationSubring ↔
    a ∈ IsLocalRing.maximalIdeal base.toDVF.valuation.valuationSubring
  rw [Valuation.mem_maximalIdeal_iff (v := vL)]
  rw [Valuation.mem_maximalIdeal_iff (v := base.toDVF.valuation)]
  have hcoe :
      ((B.inclusion vL.valuationSubring hvL_le (i a) :
        vL.valuationSubring) : L) =
        algebraMap K L (a : K) := by
    rfl
  rw [hcoe]
  exact Valuation.HasExtension.val_map_lt_one_iff base.toDVF.valuation vL (a : K)

/-- In a finite separable extension, once the actual integral closure has the
valuation-ring dichotomy, the constructed integral-closure valuation ring has a
unique prime over the base maximal ideal.
@isnad1 id=eq.3h4v.s10.8b6e3e813f21 from=translated src=- shape=068fb040 vocab=18d6d0d5
-/
theorem prime_eq_maximalIdeal_of_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal
    (base : HenselianDVF.{u, v} K)
    [Algebra.IsSeparable K L]
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (P :
      Ideal
        (ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
          (L := L) base.toDVF.valuation hval))
    (hP : P.IsPrime)
    (hcomap :
      P.comap
          (integralClosureValuationSubringIntegerMapOfMemOrInv
            (K := K) (L := L) base hval) =
        base.maximalIdeal) :
    P =
      IsLocalRing.maximalIdeal
        (ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
          (L := L) base.toDVF.valuation hval) := by
  let B :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
      (L := L) base.toDVF.valuation hval
  let i : base.valuationSubring →+* B :=
    integralClosureValuationSubringIntegerMapOfMemOrInv
      (K := K) (L := L) base hval
  let : base.toDVF.valuation.HasExtension B.valuation :=
    Valuation.integralClosureValuationSubringOfMemOrInv_hasExtension
      (L := L) base.toDVF.valuation hval
  let : IsFractionRing base.valuationSubring K :=
    base.toDVF.valuationSubring_isFractionRing
  let : IsDiscreteValuationRing base.valuationSubring :=
    base.valuationSubring_isDiscreteValuationRing
  let : IsDedekindDomain base.valuationSubring := inferInstance
  let : Algebra base.valuationSubring B := RingHom.toAlgebra i
  let : IsScalarTower base.valuationSubring B L :=
    IsScalarTower.of_algebraMap_eq (by
      intro a
      rfl)
  let : IsIntegralClosure B base.valuationSubring L :=
    Valuation.integralClosureValuationSubringOfMemOrInv_isIntegralClosure
      (L := L) base.toDVF.valuation hval
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

omit [FiniteDimensional K L] in
/-- Center-equality form of Henselian-DVF valuation uniqueness after the actual
integral closure has been turned into a valuation subring.
@isnad1 id=hasuniqu.3h4v.s10.40c3c5f50042 from=translated src=- shape=a008ed2c vocab=9725065d
-/
theorem hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_forall_center_eq_maximalIdeal
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (htargetCenter :
      ValuationSubring.idealOfLE
        (ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
          (L := L) base.toDVF.valuation hval)
        target.toDVF.valuation.valuationSubring
        (Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
          (L := L) base.toDVF.valuation target.toDVF.valuation hval) =
        IsLocalRing.maximalIdeal
          (Valuation.integralClosureValuationSubringOfMemOrInv
            (L := L) base.toDVF.valuation hval))
    (hcenter :
      ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
        (v' : _root_.Valuation L Gamma') [base.toDVF.valuation.HasExtension v'],
          ValuationSubring.idealOfLE
            (Valuation.integralClosureValuationSubringOfMemOrInv
              (L := L) base.toDVF.valuation hval)
            v'.valuationSubring
            (Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
              (L := L) base.toDVF.valuation v' hval) =
            IsLocalRing.maximalIdeal
              (Valuation.integralClosureValuationSubringOfMemOrInv
                (L := L) base.toDVF.valuation hval)) :
    HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target := by
  let B :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
      (L := L) base.toDVF.valuation hval
  have htarget_le : B ≤ target.toDVF.valuation.valuationSubring :=
    Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
      (L := L) base.toDVF.valuation target.toDVF.valuation hval
  have htarget_eq : target.toDVF.valuation.valuationSubring = B :=
    Valuation.valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdeal
      B target.toDVF.valuation.valuationSubring htarget_le
      (by simpa [B, htarget_le] using htargetCenter)
  intro Gamma' _ v' hExt
  let : base.toDVF.valuation.HasExtension v' := hExt
  have hv_le : B ≤ v'.valuationSubring :=
    Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
      (L := L) base.toDVF.valuation v' hval
  have hv_eq : v'.valuationSubring = B :=
    Valuation.valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdeal
      B v'.valuationSubring hv_le
      (by simpa [B, hv_le] using (@hcenter Gamma' inferInstance v' hExt))
  have hSubring : target.toDVF.valuation.valuationSubring = v'.valuationSubring :=
    htarget_eq.trans hv_eq.symm
  exact HenselianDVF.valuation_isEquiv_of_valuationSubring_eq base target v' hSubring

omit [FiniteDimensional K L] in
/-- Prime-uniqueness form of Henselian-DVF valuation uniqueness.
@isnad1 id=hasuniqu.1h5v.s10.c7512f5817e8 from=translated src=- shape=41ed5024 vocab=0adf9db2
-/
theorem hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_unique_primes_over_base_maximal
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (hunique :
      let B :=
        ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
          (L := L) base.toDVF.valuation hval
      let i : base.valuationSubring →+* B :=
        integralClosureValuationSubringIntegerMapOfMemOrInv
          (K := K) (L := L) base hval
      ∀ P : Ideal B, P.IsPrime → P.comap i = base.maximalIdeal →
        P = IsLocalRing.maximalIdeal B) :
    HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target := by
  let B :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
      (L := L) base.toDVF.valuation hval
  let i : base.valuationSubring →+* B :=
    integralClosureValuationSubringIntegerMapOfMemOrInv
      (K := K) (L := L) base hval
  refine
    (hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_forall_center_eq_maximalIdeal
      (K := K) (L := L) (base := base) (target := target)  hval ?_ ?_ :
        HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target)
  · let htarget_le : B ≤ target.toDVF.valuation.valuationSubring :=
      Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
        (L := L) base.toDVF.valuation target.toDVF.valuation hval
    exact hunique
      (ValuationSubring.idealOfLE B target.toDVF.valuation.valuationSubring htarget_le)
      (by infer_instance)
      (by
        simpa [B, htarget_le, i] using
          idealOfLE_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal
            (K := K) (L := L) base target.toDVF.valuation hval)
  · intro Gamma' _ v' hExt
    let : base.toDVF.valuation.HasExtension v' := hExt
    let hv_le : B ≤ v'.valuationSubring :=
      Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
        (L := L) base.toDVF.valuation v' hval
    exact hunique
      (ValuationSubring.idealOfLE B v'.valuationSubring hv_le)
      (by infer_instance)
      (by
        simpa [B, hv_le, i] using
          idealOfLE_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal
            (K := K) (L := L) base v' hval)

/-- Finite-separable Henselian-DVF uniqueness once the actual integral closure
has the valuative dichotomy.
@isnad1 id=hasuniqu.1h4v.s8.568ea1440c85 from=translated src=- shape=bb5e4a71 vocab=2a2a06b4
-/
theorem hasUniqueValuationExtension_of_integralClosure_mem_or_inv
    [Algebra.IsSeparable K L]
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring) :
    HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target :=
  (hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_unique_primes_over_base_maximal base
    target)
    hval
    (by
      let B :=
        ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
          (L := L) base.toDVF.valuation hval
      let i : base.valuationSubring →+* B :=
        integralClosureValuationSubringIntegerMapOfMemOrInv
          (K := K) (L := L) base hval
      change ∀ P : Ideal B, P.IsPrime → P.comap i = base.maximalIdeal →
        P = IsLocalRing.maximalIdeal B
      intro P hP hcomap
      exact
        prime_eq_maximalIdeal_of_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal
          (K := K) (L := L) (base := base) hval P hP hcomap)

/-- Finite-separable Henselian-DVF uniqueness once the actual integral closure
is local.
@isnad1 id=hasuniqu.0h4v.s8.ef0d0025b211 from=translated src=- shape=3582c5bd vocab=778e8764
-/
theorem hasUniqueValuationExtension_of_integralClosure_isLocalRing
    [Algebra.IsSeparable K L]
    [IsLocalRing (integralClosureIntegers base target)] :
    HenselianDVF.HasUniqueValuationExtension.{u, v, w, x, y} base target :=
  (hasUniqueValuationExtension_of_integralClosure_mem_or_inv base target)
    (integralClosure_mem_or_inv_of_isLocalRing base target)

omit [base.toDVF.valuation.HasExtension target.toDVF.valuation] in
/-- If the base Henselian-DVF valuation ring is actually complete for its
maximal-ideal topology, then the actual integral closure is Henselian along the
ideal generated by the base maximal ideal.
@isnad1 id=henselia.0h4v.s10.007a795f7cdc from=translated src=- shape=110e9b32 vocab=c84721ac
-/
theorem integralClosure_base_maximal_map_henselianRing_of_isAdicComplete
    [Algebra.IsSeparable K L]
    [IsAdicComplete base.maximalIdeal base.valuationSubring] :
    HenselianRing (integralClosureIntegers base target)
      (base.maximalIdeal.map
        (algebraMap base.valuationSubring (integralClosureIntegers base target))) := by
  let : IsNoetherianRing base.valuationSubring :=
    base.toDVF.valuationSubring_isNoetherianRing
  let : Module.Finite base.valuationSubring (integralClosureIntegers base target) :=
    (moduleFinite_integralClosureIntegers base target)
  exact
    DiscreteValuationField.henselianRing_map_algebraMap_of_moduleFinite_of_isAdicComplete
      (R := base.valuationSubring) (S := (integralClosureIntegers base target))
      (I := base.maximalIdeal)

omit [base.toDVF.valuation.HasExtension target.toDVF.valuation] in
/-- If the base Henselian-DVF valuation ring is precomplete for its
maximal-ideal topology, then the actual integral closure is Henselian along the
ideal generated by the base maximal ideal.

The separatedness needed upstairs is derived from the Henselian Jacobson
condition and finite generation, so this does not assume base adic
completeness.
@isnad1 id=henselia.0h4v.s10.1be3a368dade from=translated src=- shape=110e9b32 vocab=81c3417a
-/
theorem integralClosure_base_maximal_map_henselianRing_of_base_isPrecomplete
    [Algebra.IsSeparable K L]
    [IsPrecomplete base.maximalIdeal base.valuationSubring] :
    HenselianRing (integralClosureIntegers base target)
      (base.maximalIdeal.map
        (algebraMap base.valuationSubring (integralClosureIntegers base target))) := by
  let : IsNoetherianRing base.valuationSubring :=
    base.toDVF.valuationSubring_isNoetherianRing
  let : Module.Finite base.valuationSubring (integralClosureIntegers base target) :=
    (moduleFinite_integralClosureIntegers base target)
  have hHausR : IsHausdorff base.maximalIdeal base.valuationSubring :=
    IsHausdorff.of_le_jacobson
      (I := base.maximalIdeal) (M := base.valuationSubring)
      (show base.maximalIdeal ≤ Ideal.jacobson (⊥ : Ideal base.valuationSubring) from
        HenselianRing.jac)
  have hCompleteR : IsAdicComplete base.maximalIdeal base.valuationSubring :=
    { toIsHausdorff := hHausR
      toIsPrecomplete := inferInstance }
  let : IsAdicComplete base.maximalIdeal base.valuationSubring := hCompleteR
  exact
    DiscreteValuationField.henselianRing_map_algebraMap_of_moduleFinite_of_isAdicComplete
      (R := base.valuationSubring) (S := (integralClosureIntegers base target))
      (I := base.maximalIdeal)

omit [base.toDVF.valuation.HasExtension target.toDVF.valuation] in
/-- The actual integral closure is Henselian once finite-algebra transfer is
available over the base valuation ring.

This is the CFT-facing specialization of the finite-algebra transfer frontier:
the actual integral closure is module-finite over the Henselian base valuation
ring in a finite separable extension, so the monogenic `AdjoinRoot` transfer
route constructed in `Henselian.lean` gives the natural Henselian pair upstairs.
@isnad1 id=henselia.1h4v.s10.4b78c4ae2201 from=translated src=- shape=034ab126 vocab=1736b43a
-/
theorem integralClosure_base_maximal_map_henselianRing_of_finiteTransfer
    [Algebra.IsSeparable K L]
    (hTransfer :
      ∀ {T : Type w} [CommRing T] [Algebra base.valuationSubring T]
        [Module.Finite base.valuationSubring T],
          HenselianRing T
            (base.maximalIdeal.map
              (algebraMap base.valuationSubring T))) :
    HenselianRing (integralClosureIntegers base target)
      (base.maximalIdeal.map
        (algebraMap base.valuationSubring (integralClosureIntegers base target))) := by
  let : Module.Finite base.valuationSubring (integralClosureIntegers base target) :=
    (moduleFinite_integralClosureIntegers base target)
  change HenselianRing (integralClosure base.valuationSubring L)
    (base.maximalIdeal.map
      (algebraMap base.valuationSubring (integralClosure base.valuationSubring L)))
  exact hTransfer (T := (integralClosure base.valuationSubring L : Type w))

end ValuedExtension.Henselian

namespace HenselianDVF

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]

end HenselianDVF
end DiscreteValuationField

end

end ValuationTheory
