/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.SchemeTheory.RingTheory.GenericFiber.Finite
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.LocalGeometry.HeightOne.StandardDVF
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Normalization.Primes.AtLargerPrime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite local DVR factors and their standard DVFs

There are two logically separate steps between an ideal-theoretic
ramification calculation and the `DVF` package used by the Kummer terminal.

First, localizing a prime `q` and its contraction carries
`q.ramificationIdx R` to the maximal ideal of the literal local ring.  This
step uses no finiteness at all.

Second, when a genuinely finite map of local DVR factors has been produced
(for example by a chosen-factor or singleton-fibre theorem), its fraction
fields are finite-dimensional and its standard valuation subrings are
finite.  The standard `DVF` ramification index then agrees with the local
ideal-theoretic one.

The distinction is important: a raw prime localization of a finite algebra
need not itself be finite over the corresponding base localization.  No
such assertion is made here.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uR uS uV uW uK uL

/-- Passing simultaneously to the local rings at `q` and its contraction
identifies the original ramification index with the ramification index of
the target local ring's maximal ideal.

This is the maximal-ideal endpoint available for a raw selected prime.  It
does not require, and does not produce, module finiteness of the local map.
@isnad1 id=other.1h4v.s7.1e2dbdad2590 from=translated src=- shape=8d82b97a vocab=b898e5e8
-/
theorem localizationAtPrime_maximalIdeal_ramificationIdx_eq
    {R : Type uR} {S : Type uS}
    [CommRing R] [CommRing S] [Algebra R S]
    (q : Ideal S) [q.IsPrime] (N : ℕ)
    (hRam : q.ramificationIdx R = N) :
    let p := q.under R
    letI : p.IsPrime := Ideal.IsPrime.under R q
    letI : q.LiesOver p := ⟨rfl⟩
    let Rp := Localization.AtPrime p
    let Sq := Localization.AtPrime q
    letI : Algebra Rp Sq :=
      Localization.AtPrime.algebraOfLiesOver p q
    (IsLocalRing.maximalIdeal Sq).ramificationIdx Rp = N := by
  dsimp only
  let p := q.under R
  let : p.IsPrime := Ideal.IsPrime.under R q
  let : q.LiesOver p := ⟨rfl⟩
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let : Algebra Rp Sq :=
    Localization.AtPrime.algebraOfLiesOver p q
  have hLocal :=
    ramificationIdx_map_eq_of_isLocalization
      (R := R) (S := S) (R' := Rp) (S' := Sq)
      p.primeCompl q.primeCompl q
      (show Disjoint (q.primeCompl : Set S) (q : Set S) from
        disjoint_compl_left)
  rw [Localization.AtPrime.map_eq_maximalIdeal] at hLocal
  exact hLocal.trans hRam

/-- A finite map of domains induces a finite-dimensional extension of any
compatible chosen fraction fields.

The proof first base-changes the finite module to the source fraction field
and then uses the canonical generic-fibre equivalence.  This is the
finite-dimensionality producer used for genuine finite local DVR factors.
@isnad1 id=finitedi.0h4v.s8.45e9e22db55f from=translated src=- shape=38445859 vocab=53b94b41
-/
theorem fractionFields_finiteDimensional_of_moduleFinite
    {V : Type uV} {W : Type uW} {K : Type uK} {L : Type uL}
    [CommRing V] [IsDomain V]
    [CommRing W] [IsDomain W] [Algebra V W] [Module.Finite V W]
    [Field K] [Algebra V K] [IsFractionRing V K]
    [Field L] [Algebra W L] [IsFractionRing W L]
    [Algebra V L] [IsScalarTower V W L]
    [Algebra K L] [IsScalarTower V K L] :
    FiniteDimensional K L := by
  let eGeneric : (K ⊗[V] W) ≃ₐ[K] L :=
    finiteGenericFiberAlgEquiv
      (R := V) (C := W) (K := K) (E := L)
  let : Module.Finite K (K ⊗[V] W) :=
    Module.Finite.base_change V K W
  exact Module.Finite.equiv eGeneric.toLinearEquiv

/-- Finiteness of a genuine local DVR factor transports to the valuation
subrings of the two standard `DVF` packages.

The source and target valuation subrings are ring-equivalent to the original
DVRs.  `Module.Finite.of_equiv_equiv` transports both scalar and module
rings at once; no separability hypothesis and no raw-prime finiteness claim
is involved.
@isnad1 id=other.0h4v.s9.ab16976f82b3 from=translated src=- shape=16e40443 vocab=d01241a3
-/
theorem standardDVFOfDVR_valuationSubring_moduleFinite_of_moduleFinite
    {V : Type uV} {W : Type uW} {K : Type uK} {L : Type uL}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Algebra V W] [Module.Finite V W]
    [Field K] [Algebra V K] [IsFractionRing V K]
    [Field L] [Algebra W L] [IsFractionRing W L]
    [Algebra V L] [IsScalarTower V W L]
    [Algebra K L] [IsScalarTower V K L]
    [IsLocalHom (algebraMap V W)] :
    let base := standardDVFOfDVR V K
    let target := standardDVFOfDVR W L
    let hcomm :
        (algebraMap W L).comp (algebraMap V W) =
          (algebraMap K L).comp (algebraMap V K) := by
      rw [← IsScalarTower.algebraMap_eq V W L,
        ← IsScalarTower.algebraMap_eq V K L]
    letI : base.valuation.HasExtension target.valuation :=
      standardDVFOfDVR_hasExtension (algebraMap V W) hcomm
    Module.Finite base.valuationSubring target.valuationSubring := by
  dsimp only
  let base := standardDVFOfDVR V K
  let target := standardDVFOfDVR W L
  have hcomm :
      (algebraMap W L).comp (algebraMap V W) =
        (algebraMap K L).comp (algebraMap V K) := by
    rw [← IsScalarTower.algebraMap_eq V W L,
      ← IsScalarTower.algebraMap_eq V K L]
  let : base.valuation.HasExtension target.valuation :=
    standardDVFOfDVR_hasExtension (algebraMap V W) hcomm
  let eV : V ≃+* base.valuationSubring :=
    IsDiscreteValuationRing.equivValuationSubring (A := V) (K := K)
  let eW : W ≃+* target.valuationSubring :=
    IsDiscreteValuationRing.equivValuationSubring (A := W) (K := L)
  apply Module.Finite.of_equiv_equiv eV eW
  apply RingHom.ext
  intro z
  apply Subtype.ext
  change algebraMap K L (algebraMap V K z) =
    algebraMap W L (algebraMap V W z)
  exact (DFunLike.congr_fun hcomm z).symm

/-- Complete reusable data attached to a genuinely finite local DVR factor:

* the fraction-field extension is finite-dimensional;
* the standard valuation-subring extension is module-finite;
* the standard `DVF` ramification index is the local ideal-theoretic index.

Both finiteness conclusions are produced from `Module.Finite V W`, the
finite local factor supplied upstream.  In particular the theorem does not
take either desired standard-`DVF` conclusion as a hypothesis.
@isnad1 id=other.0h4v.s9.91f94e79f4a4 from=translated src=- shape=9931fcb5 vocab=64ac9199
-/
theorem standardDVFOfDVR_finite_ramificationData_of_moduleFinite
    {V : Type uV} {W : Type uW} {K : Type uK} {L : Type uL}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Algebra V W] [Module.Finite V W]
    [Field K] [Algebra V K] [IsFractionRing V K]
    [Field L] [Algebra W L] [IsFractionRing W L]
    [Algebra V L] [IsScalarTower V W L]
    [Algebra K L] [IsScalarTower V K L]
    [IsLocalHom (algebraMap V W)] :
    let base := standardDVFOfDVR V K
    let target := standardDVFOfDVR W L
    let hcomm :
        (algebraMap W L).comp (algebraMap V W) =
          (algebraMap K L).comp (algebraMap V K) := by
      rw [← IsScalarTower.algebraMap_eq V W L,
        ← IsScalarTower.algebraMap_eq V K L]
    letI : base.valuation.HasExtension target.valuation :=
      standardDVFOfDVR_hasExtension (algebraMap V W) hcomm
    ∃ hFiniteDimensional : FiniteDimensional K L,
      letI : FiniteDimensional K L := hFiniteDimensional
      Module.Finite base.valuationSubring target.valuationSubring ∧
        ramificationIndex base target =
          (IsLocalRing.maximalIdeal W).ramificationIdx V := by
  dsimp only
  let base := standardDVFOfDVR V K
  let target := standardDVFOfDVR W L
  have hcomm :
      (algebraMap W L).comp (algebraMap V W) =
        (algebraMap K L).comp (algebraMap V K) := by
    rw [← IsScalarTower.algebraMap_eq V W L,
      ← IsScalarTower.algebraMap_eq V K L]
  let : base.valuation.HasExtension target.valuation :=
    standardDVFOfDVR_hasExtension (algebraMap V W) hcomm
  let hFiniteDimensional : FiniteDimensional K L :=
    fractionFields_finiteDimensional_of_moduleFinite
      (V := V) (W := W) (K := K) (L := L)
  let : FiniteDimensional K L := hFiniteDimensional
  refine ⟨hFiniteDimensional, ?_, ?_⟩
  · exact
      standardDVFOfDVR_valuationSubring_moduleFinite_of_moduleFinite
        (V := V) (W := W) (K := K) (L := L)
  · exact standardDVFOfDVR_ramificationIndex_eq_ramificationIdx hcomm

/-- Numeric form of
`standardDVFOfDVR_finite_ramificationData_of_moduleFinite`.

Once the local maximal-ideal ramification index has been computed (for a raw
prime this is supplied by
`localizationAtPrime_maximalIdeal_ramificationIdx_eq`), a genuine finite DVR
factor produces exactly the finite valuation-subring data and the standard
`DVF` equality required by the exact-root/action layer.
@isnad1 id=other.1h5v.s9.54d1586f978d from=translated src=- shape=56f03ccb vocab=64ac9199
-/
theorem standardDVFOfDVR_finite_ramificationData_eq_of_moduleFinite
    {V : Type uV} {W : Type uW} {K : Type uK} {L : Type uL}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Algebra V W] [Module.Finite V W]
    [Field K] [Algebra V K] [IsFractionRing V K]
    [Field L] [Algebra W L] [IsFractionRing W L]
    [Algebra V L] [IsScalarTower V W L]
    [Algebra K L] [IsScalarTower V K L]
    [IsLocalHom (algebraMap V W)]
    (N : ℕ)
    (hRam : (IsLocalRing.maximalIdeal W).ramificationIdx V = N) :
    let base := standardDVFOfDVR V K
    let target := standardDVFOfDVR W L
    let hcomm :
        (algebraMap W L).comp (algebraMap V W) =
          (algebraMap K L).comp (algebraMap V K) := by
      rw [← IsScalarTower.algebraMap_eq V W L,
        ← IsScalarTower.algebraMap_eq V K L]
    letI : base.valuation.HasExtension target.valuation :=
      standardDVFOfDVR_hasExtension (algebraMap V W) hcomm
    ∃ hFiniteDimensional : FiniteDimensional K L,
      letI : FiniteDimensional K L := hFiniteDimensional
      Module.Finite base.valuationSubring target.valuationSubring ∧
        ramificationIndex base target = N := by
  dsimp only
  let base := standardDVFOfDVR V K
  let target := standardDVFOfDVR W L
  have hcomm :
      (algebraMap W L).comp (algebraMap V W) =
        (algebraMap K L).comp (algebraMap V K) := by
    rw [← IsScalarTower.algebraMap_eq V W L,
      ← IsScalarTower.algebraMap_eq V K L]
  let : base.valuation.HasExtension target.valuation :=
    standardDVFOfDVR_hasExtension (algebraMap V W) hcomm
  let hFiniteDimensional : FiniteDimensional K L :=
    fractionFields_finiteDimensional_of_moduleFinite
      (V := V) (W := W) (K := K) (L := L)
  let : FiniteDimensional K L := hFiniteDimensional
  refine ⟨hFiniteDimensional, ?_, ?_⟩
  · exact
      standardDVFOfDVR_valuationSubring_moduleFinite_of_moduleFinite
        (V := V) (W := W) (K := K) (L := L)
  · exact
      (standardDVFOfDVR_ramificationIndex_eq_ramificationIdx
        hcomm).trans hRam

end EtaleFundamentalGroups

end
