/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.LocalizationRing
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.DVRLocalExtension
import Tengoku.Seed.RingTheory.DedekindDomain.IntegralClosure
import Tengoku.Seed.RingTheory.DedekindDomain.Dvr
import Tengoku.Seed.RingTheory.Localization.LocalizationLocalization
import Tengoku.Seed.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Discrete valuations from localized finite integral closures

The actual localization constructed in `LocalizationRing` is a DVR in a
finite separable extension. Its canonical fraction-field valuation extends
the given base valuation, without completeness or Henselian assumptions.
-/

noncomputable section

namespace ValuationTheory.DiscreteValuationField.FiniteExtensionLocalization

universe u v w

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

attribute [local instance] localization_isLocalization

/-- The integral closure of a DVR in a finite separable extension is Dedekind.
@isnad1 id=isdedeki.0h3v.s7.79f31bf20405 from=translated src=- shape=801a044a vocab=6b6b0ec4
-/
theorem normalization_isDedekindDomain (base : DVF.{u, v} K) :
    IsDedekindDomain (Normalization (L := L) base) := by
  have : IsDiscreteValuationRing base.valuationSubring :=
    base.valuationSubring_isDiscreteValuationRing
  have : IsFractionRing base.valuationSubring K := base.valuationSubring_isFractionRing
  exact IsIntegralClosure.isDedekindDomain base.valuationSubring K L
    (Normalization (L := L) base)

omit [Algebra.IsSeparable K L] in
/-- The actual integral closure has the extension field as its fraction field.
@isnad1 id=isfracti.0h3v.s8.c620689ad83e from=translated src=- shape=2d4b5f5e vocab=fee00a12
-/
theorem normalization_isFractionRing (base : DVF.{u, v} K) :
    IsFractionRing (Normalization (L := L) base) L := by
  have : IsFractionRing base.valuationSubring K := base.valuationSubring_isFractionRing
  exact IsIntegralClosure.isFractionRing_of_finite_extension base.valuationSubring K L
    (Normalization (L := L) base)

/-- Localization at the chosen nonzero prime produces a DVR.
@isnad1 id=isdiscre.0h3v.s8.14f48d302930 from=translated src=- shape=801a044a vocab=3b0d7628
-/
theorem localization_isDiscreteValuationRing (base : DVF.{u, v} K) :
    IsDiscreteValuationRing (LocalizationRing (L := L) base) := by
  have : IsDedekindDomain (Normalization (L := L) base) := normalization_isDedekindDomain base
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    (Normalization (L := L) base) (prime_ne_bot base) (LocalizationRing (L := L) base)

omit [Algebra.IsSeparable K L] in
/-- The localization keeps the extension field as its fraction field.
@isnad1 id=isfracti.0h3v.s9.cbd31867b3c1 from=translated src=- shape=2d4b5f5e vocab=66de845e
-/
theorem localization_isFractionRing (base : DVF.{u, v} K) :
    IsFractionRing (LocalizationRing (L := L) base) L := by
  have : IsFractionRing (Normalization (L := L) base) L := normalization_isFractionRing base
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (prime (L := L) base).asIdeal.primeCompl (LocalizationRing (L := L) base) L

attribute [local instance] localization_isDiscreteValuationRing localization_isFractionRing

/-- A finite separable extension carries the discrete valuation of the localized
integral closure.-/
def dvf (base : DVF.{u, v} K) : DVF.{w, 0} L where
  ValueGroup := WithZero (Multiplicative ℤ)
  valuation := (IsDiscreteValuationRing.maximalIdeal (LocalizationRing (L := L) base)).valuation L

/-- The constructed valuation is the normalized valuation of the chosen localization.
@isnad1 id=eq.0h3v.s9.44827bd6d459 from=translated src=- shape=e9b61261 vocab=6d55ed38
-/
theorem dvf_valuation (base : DVF.{u, v} K) :
    (dvf (L := L) base).valuation =
      (IsDiscreteValuationRing.maximalIdeal (LocalizationRing (L := L) base)).valuation L := by
  rfl

/-- The constructed discrete valuation extends the original valuation on the base field.
@isnad1 id=hasexten.0h3v.s7.ca52036ba5e3 from=translated src=- shape=3cd5a9c3 vocab=01ba2504
-/
theorem dvf_hasExtension (base : DVF.{u, v} K) :
    base.valuation.HasExtension (dvf (L := L) base).valuation := by
  have : IsLocalHom (algebraMap base.valuationSubring (LocalizationRing (L := L) base)) :=
    baseMap_isLocalHom base
  exact hasExtension_dvr_valuation_of_isLocalHom base (LocalizationRing (L := L) base)

end ValuationTheory.DiscreteValuationField.FiniteExtensionLocalization
