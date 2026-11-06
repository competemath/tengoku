/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Degree

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Uniqueness criteria for complete discretely valued field extensions

Uniqueness is stated up to equivalence of extension valuations. Integral-closure
valuation subrings, local centers, and fibers provide concrete criteria, while
the corresponding Henselian-field results are transferred to complete fields.
The module also records criteria from finite modules and adic completeness.
-/

namespace ValuationTheory

noncomputable section

universe u v w x y

namespace DiscreteValuationField
namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- A complete-DVF uniqueness predicate for extensions of the base valuation.-/
def HasUniqueValuationExtension (base : CompleteDVF.{u, v} K)
    (target : CompleteDVF.{w, x} L) : Prop :=
  ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
      target.valuation.IsEquiv v'

omit [FiniteDimensional K L] [base.valuation.HasExtension target.valuation] in
/-- Equality of valuation subrings for all extensions proves uniqueness up to
mathlib's valuation equivalence.-/
theorem hasUniqueValuationExtension_of_forall_valuationSubring_eq
    (h :
      ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
        (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
          target.valuation.valuationSubring = v'.valuationSubring) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  intro Gamma' _ v' _
  exact valuation_isEquiv_of_valuationSubring_eq target v' (@h Gamma' _ v' _)

omit [FiniteDimensional K L] in
/-- Finite-module criterion for uniqueness of valuation extensions.  If every
valuation extending the base valuation has a module-finite valuation ring over
the base valuation ring, then the extension valuation is unique up to mathlib's
valuation equivalence.-/
theorem hasUniqueValuationExtension_of_forall_moduleFinite
    [Module.Finite base.valuationSubring target.valuationSubring]
    (hfinite :
      ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
        (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
          [Algebra base.valuation.valuationSubring v'.valuationSubring] →
          Module.Finite base.valuation.valuationSubring v'.valuationSubring) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  intro Gamma' _ v' hExt
  let : base.valuation.HasExtension v' := hExt
  let : Module.Finite base.valuation.valuationSubring v'.valuationSubring :=
    @hfinite Gamma' inferInstance v' hExt inferInstance
  let : Module.Finite base.valuation.valuationSubring
      target.valuation.valuationSubring := by
    change Module.Finite base.valuationSubring target.valuationSubring
    infer_instance
  exact
    Valuation.valuation_isEquiv_of_hasExtension_of_moduleFinite
      (L := L) base.valuation target.valuation v'

/-- Integral-closure criterion for uniqueness of valuation extensions.  In a
finite separable extension over a complete DVF, if the chosen target valuation
ring and every comparison valuation ring extending the base valuation are the
actual integral closure of the base valuation ring in `L`, then the extension
valuation is unique up to mathlib's valuation equivalence.

For the Henselian finite-extension theorem, this isolates the remaining
frontier: prove the integral-closure statement for all extension valuations
from the Henselian hypothesis, rather than adding a certificate carrying
uniqueness.-/
theorem hasUniqueValuationExtension_of_forall_isIntegralClosure
    [Algebra.IsSeparable K L]
    [IsIntegralClosure target.valuationSubring base.valuationSubring L]
    (hintegral :
      ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
        (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
          [Algebra base.valuation.valuationSubring v'.valuationSubring] →
          IsIntegralClosure v'.valuationSubring base.valuation.valuationSubring L) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  let : IsNoetherianRing base.valuationSubring :=
    base_valuationSubring_isNoetherianRing (K := K) base
  let : IsIntegralClosure target.valuation.valuationSubring
      base.valuation.valuationSubring L := by
    change IsIntegralClosure target.valuationSubring base.valuationSubring L
    infer_instance
  let : Module.Finite base.valuation.valuationSubring
      target.valuation.valuationSubring :=
    Valuation.moduleFinite_valuationSubring_of_isIntegralClosure
      (L := L) base.valuation target.valuation
  intro Gamma' _ v' hExt
  let : base.valuation.HasExtension v' := hExt
  let : IsIntegralClosure v'.valuationSubring base.valuation.valuationSubring L :=
    @hintegral Gamma' inferInstance v' hExt inferInstance
  let : Module.Finite base.valuation.valuationSubring v'.valuationSubring :=
    Valuation.moduleFinite_valuationSubring_of_isIntegralClosure
      (L := L) base.valuation v'
  exact
    Valuation.valuation_isEquiv_of_hasExtension_of_moduleFinite
      (L := L) base.valuation target.valuation v'

/-- If the chosen target valuation ring and every comparison valuation ring
extending the base valuation are integral over the base valuation ring, then
the valuation extension is unique.

This is the non-certificate Henselian frontier reduction: to prove uniqueness
over a Henselian base it is now enough to prove the actual integrality of each
extension valuation ring, because the preceding Chevalley bridge identifies
such valuation rings with the actual integral closure.-/
theorem hasUniqueValuationExtension_of_forall_isIntegral
    [Algebra.IsSeparable K L]
    [Algebra.IsIntegral base.valuationSubring target.valuationSubring]
    (hintegral :
      ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
        (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
          [Algebra base.valuation.valuationSubring v'.valuationSubring] →
          Algebra.IsIntegral base.valuation.valuationSubring v'.valuationSubring) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  let : Algebra.IsIntegral base.valuation.valuationSubring
      target.valuation.valuationSubring := by
    change Algebra.IsIntegral base.valuationSubring target.valuationSubring
    infer_instance
  let : IsNoetherianRing base.valuationSubring :=
    base_valuationSubring_isNoetherianRing (K := K) base
  let : IsIntegralClosure target.valuation.valuationSubring
      base.valuation.valuationSubring L :=
    Valuation.valuationSubring_isIntegralClosure_of_isIntegral
      (L := L) base.valuation target.valuation
  let : Module.Finite base.valuation.valuationSubring
      target.valuation.valuationSubring :=
    Valuation.moduleFinite_valuationSubring_of_isIntegralClosure
      (L := L) base.valuation target.valuation
  intro Gamma' _ v' hExt
  let : base.valuation.HasExtension v' := hExt
  let : Algebra.IsIntegral base.valuation.valuationSubring v'.valuationSubring :=
    @hintegral Gamma' inferInstance v' hExt inferInstance
  let : IsIntegralClosure v'.valuationSubring base.valuation.valuationSubring L :=
    Valuation.valuationSubring_isIntegralClosure_of_isIntegral
      (L := L) base.valuation v'
  let : Module.Finite base.valuation.valuationSubring v'.valuationSubring :=
    Valuation.moduleFinite_valuationSubring_of_isIntegralClosure
      (L := L) base.valuation v'
  exact
    Valuation.valuation_isEquiv_of_hasExtension_of_moduleFinite
      (L := L) base.valuation target.valuation v'

omit [FiniteDimensional K L] in
open _root_.ValuationTheory.DiscreteValuationField.Valuation in
/-- Valuation-ring form of the Henselian uniqueness frontier.

If the actual integral closure of the base valuation ring in `L` has the
valuation-ring dichotomy, and every valuation extension is a local overring of
that integral-closure valuation subring, then the base valuation has a unique
extension to `L` up to mathlib valuation equivalence.

The remaining Henselian theorem is not hidden in a certificate here: it is
precisely the proof of the dichotomy and local-overring condition from the
Henselian hypotheses.  This theorem performs the actual Chevalley plus
valuation-overring collapse step.-/
theorem hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_forall_local_inclusion
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (htargetLocal :
      IsLocalHom
        ((ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
            (L := L) base.valuation hval).inclusion
          target.valuation.valuationSubring
          (Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
            (L := L) base.valuation target.valuation hval)))
    (hlocal :
      ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
        (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
          IsLocalHom
            ((Valuation.integralClosureValuationSubringOfMemOrInv
                (L := L) base.valuation hval).inclusion
              v'.valuationSubring
              (integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
                (L := L) base.valuation v' hval))) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  let B :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
      (L := L) base.valuation hval
  have htarget_le : B ≤ target.valuation.valuationSubring :=
    Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
      (L := L) base.valuation target.valuation hval
  have htarget_eq : target.valuation.valuationSubring = B := by
    let : IsLocalHom (B.inclusion target.valuation.valuationSubring htarget_le) :=
      htargetLocal
    exact
      Valuation.valuationSubring_eq_of_le_of_inclusion_isLocalHom
        B target.valuation.valuationSubring htarget_le
  intro Gamma' _ v' hExt
  let : base.valuation.HasExtension v' := hExt
  have hv_le : B ≤ v'.valuationSubring :=
    Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
      (L := L) base.valuation v' hval
  have hv_eq : v'.valuationSubring = B := by
    let : IsLocalHom (B.inclusion v'.valuationSubring hv_le) :=
      @hlocal Gamma' inferInstance v' hExt
    exact
      Valuation.valuationSubring_eq_of_le_of_inclusion_isLocalHom
        B v'.valuationSubring hv_le
  have hSubring : target.valuation.valuationSubring = v'.valuationSubring :=
    htarget_eq.trans hv_eq.symm
  exact valuation_isEquiv_of_valuationSubring_eq target v' hSubring

omit [FiniteDimensional K L] in
/-- Center-prime form of the Henselian uniqueness frontier.

If the actual integral closure of the base valuation ring is a valuation ring,
and the center of every extension valuation ring on that integral-closure
valuation ring is the maximal ideal, then the extension valuation is unique.

This is the exact prime-theoretic step that remains after proving the
Henselian valuative dichotomy: the hypotheses are the center equalities
the Henselian finite-extension theorem must supply, not local-map or
certificate-style substitutes.-/
theorem hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_forall_center_eq_maximalIdeal
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (htargetCenter :
      ValuationSubring.idealOfLE
        (ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
          (L := L) base.valuation hval)
        target.valuation.valuationSubring
        (Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
          (L := L) base.valuation target.valuation hval) =
        IsLocalRing.maximalIdeal
          (Valuation.integralClosureValuationSubringOfMemOrInv
            (L := L) base.valuation hval))
    (hcenter :
      ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
        (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
          ValuationSubring.idealOfLE
            (Valuation.integralClosureValuationSubringOfMemOrInv
              (L := L) base.valuation hval)
            v'.valuationSubring
            (Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
              (L := L) base.valuation v' hval) =
            IsLocalRing.maximalIdeal
              (Valuation.integralClosureValuationSubringOfMemOrInv
                (L := L) base.valuation hval)) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  let B :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
      (L := L) base.valuation hval
  have htarget_le : B ≤ target.valuation.valuationSubring :=
    Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
      (L := L) base.valuation target.valuation hval
  have htarget_eq : target.valuation.valuationSubring = B :=
    Valuation.valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdeal
      B target.valuation.valuationSubring htarget_le
      (by simpa [B, htarget_le] using htargetCenter)
  intro Gamma' _ v' hExt
  let : base.valuation.HasExtension v' := hExt
  have hv_le : B ≤ v'.valuationSubring :=
    Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
      (L := L) base.valuation v' hval
  have hv_eq : v'.valuationSubring = B :=
    Valuation.valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdeal
      B v'.valuationSubring hv_le
      (by simpa [B, hv_le] using (@hcenter Gamma' inferInstance v' hExt))
  have hSubring : target.valuation.valuationSubring = v'.valuationSubring :=
    htarget_eq.trans hv_eq.symm
  exact valuation_isEquiv_of_valuationSubring_eq target v' hSubring

omit [FiniteDimensional K L] in
/-- Prime-uniqueness form of the Henselian uniqueness frontier.

After the actual integral closure has been turned into a valuation subring, it
is enough to prove that every prime of that valuation subring whose contraction
to the base valuation ring is the base maximal ideal is itself the maximal
ideal.  The center of each extension valuation ring has exactly that
contraction, so this theorem converts the Henselian local prime-uniqueness
statement into uniqueness of valuation extensions.-/
theorem hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_unique_primes_over_base_maximal
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (hunique :
      let B :=
        ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
          (L := L) base.valuation hval
      let i : base.valuationSubring →+* B :=
        integralClosureValuationSubringIntegerMapOfMemOrInv
          (K := K) (L := L) base hval
      ∀ P : Ideal B, P.IsPrime → P.comap i = base.maximalIdeal →
        P = IsLocalRing.maximalIdeal B) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  let B :=
    ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
      (L := L) base.valuation hval
  let i : base.valuationSubring →+* B :=
    integralClosureValuationSubringIntegerMapOfMemOrInv
      (K := K) (L := L) base hval
  refine
    (hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_forall_center_eq_maximalIdeal
      (K := K) (L := L) (base := base) (target := target)  hval ?_ ?_ :
        HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target))
  · let htarget_le : B ≤ target.valuation.valuationSubring :=
      Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
        (L := L) base.valuation target.valuation hval
    exact hunique
      (ValuationSubring.idealOfLE B target.valuation.valuationSubring htarget_le)
      (by infer_instance)
      (by
        simpa [B, htarget_le, i] using
          idealOfLE_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal
            (K := K) (L := L) base target.valuation hval)
  · intro Gamma' _ v' hExt
    let : base.valuation.HasExtension v' := hExt
    let hv_le : B ≤ v'.valuationSubring :=
      Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
        (L := L) base.valuation v' hval
    exact hunique
      (ValuationSubring.idealOfLE B v'.valuationSubring hv_le)
      (by infer_instance)
      (by
        simpa [B, hv_le, i] using
          idealOfLE_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal
            (K := K) (L := L) base v' hval)

/-- Finite-separable form of the Henselian uniqueness bridge.

After the Henselian part proves the valuative dichotomy for the actual
integral closure, finite separability supplies the prime uniqueness over the
base maximal ideal by Dedekind theory.  Thus no separate local-map, center
equality, integral-inclusion, or module-finiteness certificates are needed to
deduce uniqueness of the valuation extension.-/
theorem hasUniqueValuationExtension_of_integralClosure_mem_or_inv
    [Algebra.IsSeparable K L]
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) :=
  (hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_unique_primes_over_base_maximal base
    target)
    hval
    (by
      let B :=
        ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
          (L := L) base.valuation hval
      let i : base.valuationSubring →+* B :=
        integralClosureValuationSubringIntegerMapOfMemOrInv
          (K := K) (L := L) base hval
      change ∀ P : Ideal B, P.IsPrime → P.comap i = base.maximalIdeal →
        P = IsLocalRing.maximalIdeal B
      intro P hP hcomap
      exact
        prime_eq_maximalIdeal_of_comap_integralClosureValuationSubringIntegerMap_eq_maximalIdeal
          (K := K) (L := L) (base := base) hval P hP hcomap)

/-- Finite-separable uniqueness once the chosen target valuation ring has been
identified as the actual integral closure of the base valuation ring.

The proof first turns the integral-closure identification into the valuative
dichotomy for `integralClosure base.valuationSubring L`; the finite-separable
Dedekind/local bridge above then supplies uniqueness of all valuation
extensions.-/
theorem hasUniqueValuationExtension_of_target_valuationSubring_isIntegralClosure
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    [IsIntegralClosure target.valuationSubring base.valuationSubring L] :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) :=
  (hasUniqueValuationExtension_of_integralClosure_mem_or_inv base target)
    (integralClosure_mem_or_inv_of_target_valuationSubring_isIntegralClosure
      (K := K) (L := L) base target)

/-- Finite-separable uniqueness once the chosen target valuation ring is
module-finite over the base valuation ring.

This is a theorem-level bridge, not a certificate package: module-finiteness
identifies the target valuation ring with the actual integral closure, and the
preceding theorem converts that identification into uniqueness of valuation
extensions.-/
theorem hasUniqueValuationExtension_of_target_moduleFinite
    [Algebra.IsSeparable K L]
    [Module.Finite base.valuationSubring target.valuationSubring]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  let : IsIntegralClosure target.valuationSubring base.valuationSubring L :=
    target_valuationSubring_isIntegralClosure_of_moduleFinite
      (K := K) (L := L) base target
  exact
    (hasUniqueValuationExtension_of_target_valuationSubring_isIntegralClosure
      (K := K) (L := L) (base := base) (target := target)  :
        HasUniqueValuationExtension.{u, v, w, x, y}
          (base := base) (target := target))

/-- Finite-separable uniqueness once the actual integral closure is known to be
a valuation ring.

This is the local/DVR-facing form of the frontier: a Henselian proof may first
show that the finite integral closure is local, hence a valuation ring, and
then this theorem supplies uniqueness through the proven finite-separable
Dedekind/local bridge.-/
theorem hasUniqueValuationExtension_of_integralClosure_valuationRing
    [Algebra.IsSeparable K L]
    [ValuationRing (integralClosureIntegers base target)] :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) :=
  (hasUniqueValuationExtension_of_integralClosure_mem_or_inv base target)
    ((integralClosure_mem_or_inv_of_integralClosure_valuationRing base target))

/-- Finite-separable uniqueness once the actual integral closure is local.

This is the sharpened Henselian frontier: after the Henselian argument proves
that the finite integral closure is a local ring, Dedekind theory makes it a
valuation ring and the valuative-dichotomy bridge above supplies uniqueness of
all valuation extensions.-/
theorem hasUniqueValuationExtension_of_integralClosure_isLocalRing
    [Algebra.IsSeparable K L]
    [IsLocalRing (integralClosureIntegers base target)] :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) :=
  (hasUniqueValuationExtension_of_integralClosure_mem_or_inv base target)
    (integralClosure_mem_or_inv_of_isLocalRing base target)

omit [FiniteDimensional K L] in
/-- Integral-inclusion form of the Henselian uniqueness frontier.

Once the actual integral closure has been shown to be a valuation ring, it is
enough to prove that the inclusions from that valuation ring into every
extension valuation ring are integral.  The center equalities needed for the
valuation-overring collapse then follow from going-up for integral maps between
local rings, not from a separate center certificate.-/
theorem hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_forall_integral_inclusion
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (htargetIntegral :
      let B :=
        ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
          (L := L) base.valuation hval
      let htarget_le : B ≤ target.valuation.valuationSubring :=
        Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
          (L := L) base.valuation target.valuation hval
      (B.inclusion target.valuation.valuationSubring htarget_le).IsIntegral)
    (hintegral :
      ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
        (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
          let B :=
            Valuation.integralClosureValuationSubringOfMemOrInv
              (L := L) base.valuation hval
          let hv_le : B ≤ v'.valuationSubring :=
            Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
              (L := L) base.valuation v' hval
          (B.inclusion v'.valuationSubring hv_le).IsIntegral) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  refine
    (hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_forall_center_eq_maximalIdeal base
      target)
      hval ?_ ?_
  · let B :=
      ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
        (L := L) base.valuation hval
    let htarget_le : B ≤ target.valuation.valuationSubring :=
      Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
        (L := L) base.valuation target.valuation hval
    exact idealOfLE_eq_maximalIdeal_of_isIntegral B target.valuation.valuationSubring
      htarget_le (by simpa [B, htarget_le] using htargetIntegral)
  · intro Gamma' _ v' hExt
    let : base.valuation.HasExtension v' := hExt
    let B :=
      ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
        (L := L) base.valuation hval
    let hv_le : B ≤ v'.valuationSubring :=
      Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
        (L := L) base.valuation v' hval
    exact idealOfLE_eq_maximalIdeal_of_isIntegral B v'.valuationSubring hv_le
      (by simpa [B, hv_le] using (@hintegral Gamma' inferInstance v' hExt))

omit [FiniteDimensional K L] in
/-- Finite-inclusion form of the Henselian uniqueness frontier.

This is useful when the Henselian argument proves finite generation of the
valuation-overring inclusions rather than integrality directly.-/
theorem hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_forall_finite_inclusion
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (htargetFinite :
      let B :=
        ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
          (L := L) base.valuation hval
      let htarget_le : B ≤ target.valuation.valuationSubring :=
        Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
          (L := L) base.valuation target.valuation hval
      (B.inclusion target.valuation.valuationSubring htarget_le).Finite)
    (hfinite :
      ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
        (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
          let B :=
            Valuation.integralClosureValuationSubringOfMemOrInv
              (L := L) base.valuation hval
          let hv_le : B ≤ v'.valuationSubring :=
            Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
              (L := L) base.valuation v' hval
          (B.inclusion v'.valuationSubring hv_le).Finite) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  refine
    (hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_forall_integral_inclusion base
      target)
      hval ?_ ?_
  · let B :=
      ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
        (L := L) base.valuation hval
    let htarget_le : B ≤ target.valuation.valuationSubring :=
      Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
        (L := L) base.valuation target.valuation hval
    have htargetFinite' :
        (B.inclusion target.valuation.valuationSubring htarget_le).Finite := by
      simpa [B, htarget_le] using htargetFinite
    exact htargetFinite'.to_isIntegral
  · intro Gamma' _ v' hExt
    let : base.valuation.HasExtension v' := hExt
    let B :=
      ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
        (L := L) base.valuation hval
    let hv_le : B ≤ v'.valuationSubring :=
      Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
        (L := L) base.valuation v' hval
    have hvFinite :
        (B.inclusion v'.valuationSubring hv_le).Finite := by
      simpa [B, hv_le] using
        (@hfinite Gamma' inferInstance v' hExt)
    exact hvFinite.to_isIntegral

omit [FiniteDimensional K L] in
/-- Elementwise center form of the Henselian uniqueness frontier.

After proving that the actual integral closure is a valuation ring, it is
enough to check centers by maximal-ideal membership along the inclusions into
the target valuation ring and every comparison extension valuation ring.  This
is the form closest to the remaining Henselian argument: one proves an
element of the integral closure is nonunit exactly when its image in the
extension valuation ring is nonunit, and the valuation-overring collapse is
then automatic.-/
theorem hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_forall_center_mem_iff
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (htargetCenterMem :
      let B :=
        ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
          (L := L) base.valuation hval
      let htarget_le : B ≤ target.valuation.valuationSubring :=
        Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
          (L := L) base.valuation target.valuation hval
      ∀ x : B,
        B.inclusion target.valuation.valuationSubring htarget_le x ∈
            IsLocalRing.maximalIdeal target.valuation.valuationSubring ↔
          x ∈ IsLocalRing.maximalIdeal B)
    (hcenterMem :
      ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
        (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
          let B :=
            Valuation.integralClosureValuationSubringOfMemOrInv
              (L := L) base.valuation hval
          let hv_le : B ≤ v'.valuationSubring :=
            Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
              (L := L) base.valuation v' hval
          ∀ x : B,
            B.inclusion v'.valuationSubring hv_le x ∈
                IsLocalRing.maximalIdeal v'.valuationSubring ↔
              x ∈ IsLocalRing.maximalIdeal B) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  refine
    (hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_forall_center_eq_maximalIdeal
      (K := K) (L := L) (base := base) (target := target)  hval ?_ ?_ :
        HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target))
  · let B :=
      ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
        (L := L) base.valuation hval
    let htarget_le : B ≤ target.valuation.valuationSubring :=
      Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
        (L := L) base.valuation target.valuation hval
    exact
      Valuation.idealOfLE_eq_maximalIdeal_of_mem_maximalIdeal_iff
        B target.valuation.valuationSubring htarget_le
        (by simpa [B, htarget_le] using htargetCenterMem)
  · intro Gamma' _ v' hExt
    let : base.valuation.HasExtension v' := hExt
    let B :=
      ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
        (L := L) base.valuation hval
    let hv_le : B ≤ v'.valuationSubring :=
      Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
        (L := L) base.valuation v' hval
    exact
      Valuation.idealOfLE_eq_maximalIdeal_of_mem_maximalIdeal_iff
        B v'.valuationSubring hv_le
        (by simpa [B, hv_le] using (@hcenterMem Gamma' inferInstance v' hExt))

omit [FiniteDimensional K L] in
/-- One-sided elementwise center form of the Henselian uniqueness frontier.

For inclusions of local rings, the implication from target nonunit to source
nonunit is automatic.  Thus, after proving that the actual integral closure is
a valuation ring, the remaining center work is only to show that elements in the
maximal ideal of the integral-closure valuation ring map into the maximal ideals
of the extension valuation rings.-/
theorem hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_forall_center_mem
    (hval :
      ∀ z : L,
        z ∈ (integralClosure base.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure base.valuationSubring L).toSubring)
    (htargetCenterMem :
      let B :=
        ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
          (L := L) base.valuation hval
      let htarget_le : B ≤ target.valuation.valuationSubring :=
        Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
          (L := L) base.valuation target.valuation hval
      ∀ x : B,
        x ∈ IsLocalRing.maximalIdeal B →
          B.inclusion target.valuation.valuationSubring htarget_le x ∈
            IsLocalRing.maximalIdeal target.valuation.valuationSubring)
    (hcenterMem :
      ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
        (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
          let B :=
            Valuation.integralClosureValuationSubringOfMemOrInv
              (L := L) base.valuation hval
          let hv_le : B ≤ v'.valuationSubring :=
            Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
              (L := L) base.valuation v' hval
          ∀ x : B,
            x ∈ IsLocalRing.maximalIdeal B →
              B.inclusion v'.valuationSubring hv_le x ∈
                IsLocalRing.maximalIdeal v'.valuationSubring) :
    HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target) := by
  refine
    (hasUniqueValuationExtension_of_integralClosure_mem_or_inv_of_forall_center_mem_iff base target)
      hval ?_ ?_
  · let B :=
      ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
        (L := L) base.valuation hval
    let htarget_le : B ≤ target.valuation.valuationSubring :=
      Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
        (L := L) base.valuation target.valuation hval
    change ∀ x : B,
      B.inclusion target.valuation.valuationSubring htarget_le x ∈
          IsLocalRing.maximalIdeal target.valuation.valuationSubring ↔
        x ∈ IsLocalRing.maximalIdeal B
    intro x
    constructor
    · intro hx
      exact mem_maximalIdeal_of_map_mem_maximalIdeal
        (B.inclusion target.valuation.valuationSubring htarget_le) hx
    · intro hx
      simpa [B, htarget_le] using htargetCenterMem x hx
  · intro Gamma' _ v' hExt
    let : base.valuation.HasExtension v' := hExt
    let B :=
      ValuationTheory.DiscreteValuationField.Valuation.integralClosureValuationSubringOfMemOrInv
        (L := L) base.valuation hval
    let hv_le : B ≤ v'.valuationSubring :=
      Valuation.integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension
        (L := L) base.valuation v' hval
    change ∀ x : B,
      B.inclusion v'.valuationSubring hv_le x ∈
          IsLocalRing.maximalIdeal v'.valuationSubring ↔
        x ∈ IsLocalRing.maximalIdeal B
    intro x
    constructor
    · intro hx
      exact mem_maximalIdeal_of_map_mem_maximalIdeal
        (B.inclusion v'.valuationSubring hv_le) hx
    · intro hx
      simpa [B, hv_le] using
        (@hcenterMem Gamma' inferInstance v' hExt x hx)

omit [FiniteDimensional K L] [base.valuation.HasExtension target.valuation] in
/-- The valuation-subring equality consequence of unique valuation extension.-/
theorem valuationSubring_eq_of_hasUniqueValuationExtension
    (huniq : HasUniqueValuationExtension.{u, v, w, x, y} (base := base) (target := target))
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'] :
    target.valuation.valuationSubring = v'.valuationSubring :=
  valuationSubring_eq_of_valuation_isEquiv target (@huniq Gamma' _ v' _)

omit [FiniteDimensional K L] [base.valuation.HasExtension target.valuation] in
/-- Under unique extension, the actual valuation produced by Chevalley's
theorem can be chosen together with all construction data and is equivalent to
the chosen target valuation.  This is the finite-extension frontier form of
Chevalley plus uniqueness: it does not merely return a valuation subring, but
keeps the extension valuation, exact base pullback, integral-closure
containment, local map, residue injection, valuation equivalence, and
valuation-ring equality for the same witness.-/
theorem exists_chevalley_extension_valuation_eq_target_of_hasUniqueValuationExtension
    (huniq : HasUniqueValuationExtension.{u, v, w, x, w}
      (base := base) (target := target)) :
    ∃ ΓL : Type w,
      ∃ _ : LinearOrderedCommGroupWithZero ΓL,
        ∃ vL : _root_.Valuation L ΓL,
          ∃ hExt : base.valuation.HasExtension vL,
            letI : base.valuation.HasExtension vL := hExt
            letI : Algebra base.valuationSubring vL.valuationSubring := by
              change Algebra base.valuation.valuationSubring vL.valuationSubring
              infer_instance
            letI : IsLocalHom
                (algebraMap base.valuationSubring vL.valuationSubring) := by
              exact Valuation.integerMap_isLocalHom_of_hasExtension
                base.valuation vL
            (∀ a : K, algebraMap K L a ∈ vL.valuationSubring ↔
              a ∈ base.valuation.valuationSubring) ∧
            (∀ z : integralClosure base.valuationSubring L,
              (z : L) ∈ vL.valuationSubring) ∧
            (IsLocalRing.maximalIdeal vL.valuationSubring).LiesOver
              (IsLocalRing.maximalIdeal base.valuationSubring) ∧
            IsLocalHom
              (algebraMap base.valuationSubring vL.valuationSubring) ∧
            Function.Injective
              (IsLocalRing.ResidueField.map
                (algebraMap base.valuationSubring vL.valuationSubring)) ∧
            target.valuation.IsEquiv vL ∧
            target.valuation.valuationSubring = vL.valuationSubring := by
  obtain ⟨ΓL, hΓL, vL, hExt, hpullback, hIntegral, hlies, hlocal,
      hResidue⟩ :=
    Valuation.chevalley_exists_extension_valuation_with_pullback_integralClosure_local_data
      (L := L) base.valuation
  let : LinearOrderedCommGroupWithZero ΓL := hΓL
  let : base.valuation.HasExtension vL := hExt
  let : Algebra base.valuationSubring vL.valuationSubring := by
    change Algebra base.valuation.valuationSubring vL.valuationSubring
    infer_instance
  let : IsLocalHom
      (algebraMap base.valuationSubring vL.valuationSubring) := by
    exact Valuation.integerMap_isLocalHom_of_hasExtension
      base.valuation vL
  have hEquiv : target.valuation.IsEquiv vL :=
    @huniq ΓL inferInstance vL inferInstance
  have hSubring : target.valuation.valuationSubring = vL.valuationSubring :=
    valuationSubring_eq_of_valuation_isEquiv target hEquiv
  exact ⟨ΓL, inferInstance, vL, inferInstance, hpullback, hIntegral, hlies,
    hlocal, hResidue, hEquiv, hSubring⟩

/-- If the chosen target valuation ring is an actual integral closure of the base
valuation ring in `L`, it is canonically equivalent to mathlib's
`integralClosure`.-/
noncomputable def integralClosureEquivValuationSubring
    [Algebra base.valuationSubring L]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    [IsIntegralClosure target.valuationSubring base.valuationSubring L] :
    (integralClosure base.valuationSubring L) ≃ₐ[base.valuationSubring]
      target.valuationSubring :=
  IsIntegralClosure.equiv base.valuationSubring
    (integralClosure base.valuationSubring L) L target.valuationSubring

end ValuedExtension
end DiscreteValuationField

end

end ValuationTheory
