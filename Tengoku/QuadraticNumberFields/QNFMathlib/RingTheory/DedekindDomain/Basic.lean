/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Tengoku.Seed.RingTheory.DedekindDomain.Basic
import Tengoku.Seed.RingTheory.IntegralClosure.IntegrallyClosed
import Tengoku.Seed.RingTheory.Noetherian.Basic
import Tengoku.QuadraticNumberFields.QNFMathlib.RingTheory.Krull

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Dedekind-Domain Transport Across Ring Equivalences

Material destined for mathlib.
-/

namespace RingEquiv

section CommRing

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Transport `IsDedekindDomain` across a ring equivalence.

A Dedekind domain is characterized by: (1) Noetherian, (2) domain,
(3) integrally closed, (4) dimension ≤ 1. Each of these is individually
invariant under ring isomorphism, so the conjunction is as well.
@isnad1 id=isdedeki.0h3v.s5.a1dee7908332 from=translated src=- shape=0751dee6 vocab=f39244da
-/
-- Repository use: `QuadraticField/Transport.lean`, `Zsqrtd/Dedekind.lean`, and
-- `Zsqrtd/MathlibInstances.lean` use this to transport Dedekind-domain
-- structures across ring equivalences.
theorem isDedekindDomain (e : R ≃+* S) [IsDedekindDomain R] :
    IsDedekindDomain S := by
  letI : IsNoetherianRing R :=
    show IsNoetherian R R from IsDedekindRing.toIsNoetherian
  letI : IsDomain S := e.toMulEquiv.isDomain_iff.mp inferInstance
  letI : IsNoetherianRing S := isNoetherianRing_of_ringEquiv R e
  letI : IsIntegrallyClosed S := IsIntegrallyClosed.of_equiv e
  letI : Ring.DimensionLEOne S := dimensionLEOne e
  letI : IsDedekindRing S :=
    { toIsNoetherian := show IsNoetherian S S from inferInstance
      toDimensionLEOne := inferInstance
      toIsIntegralClosure :=
        show IsIntegralClosure S S (FractionRing S) from inferInstance }
  infer_instance

/-- `IsDedekindDomain` is invariant under ring equivalence.
@isnad1 id=iff.0h3v.s5.c091d81e38fb from=translated src=- shape=b720df5a vocab=f39244da
-/
-- Repository use: currently support API for the forward transport theorem above;
-- no direct non-patch reference is expected yet.
theorem isDedekindDomain_iff (e : R ≃+* S) :
    IsDedekindDomain R ↔ IsDedekindDomain S := by
  constructor
  · intro _
    exact isDedekindDomain e
  · intro _
    exact isDedekindDomain e.symm

end CommRing

end RingEquiv
