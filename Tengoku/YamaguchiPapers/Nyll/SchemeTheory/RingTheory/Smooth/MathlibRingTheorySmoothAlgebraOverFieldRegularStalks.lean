/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_RingTheory_SmoothAlgebraOverFieldRegularStalks.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Tengoku.Seed.RingTheory.DualNumber
import Tengoku.Seed.RingTheory.LocalProperties.Reduced
import Tengoku.Seed.RingTheory.RegularLocalRing.Defs
import Tengoku.Seed.RingTheory.Unramified.Field

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Regular stalks for unramified algebras over fields

The dual-number counterexample records why a smoothness hypothesis is needed.
-/

universe u

open IsLocalRing

/-- Smooth algebras over fields have regular localizations at prime ideals.-/
def SmoothFieldFiberRegularStalksInput : Prop :=
  ∀ (k A : Type u) [Field k] [CommRing A] [Algebra k A],
    Algebra.Smooth k A → ∀ (p : Ideal A) [p.IsPrime],
      IsRegularLocalRing (Localization.AtPrime p)

namespace SmoothFieldFiberRegularStalks

/--
@isnad1 id=isregula.1h1v.s4.154c38a8e620 from=translated src=- shape=c612a321 vocab=ad624774
-/
theorem isRegularLocalRing_of_isField (R : Type*) [CommRing R] (hf : IsField R) :
    IsRegularLocalRing R := by
  let : Field R := IsField.toField hf
  infer_instance

/--
@isnad1 id=isregula.0h2v.s6.dbccd3e1bc7d from=translated src=- shape=364b0745 vocab=2c613493
-/
theorem isRegularLocalRing_atPrime_of_artinian_reduced
    (A : Type*) [CommRing A] [IsArtinianRing A] [IsReduced A]
    (p : Ideal A) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) :=
  isRegularLocalRing_of_isField _
    (IsArtinianRing.isField_of_isReduced_of_isLocalRing (Localization.AtPrime p))

/--
@isnad1 id=isregula.0h1v.s5.04e2beed09ca from=translated src=- shape=affebb5f vocab=ba65873e
-/
theorem isRegularRing_of_isArtinianRing_of_isReduced
    (A : Type*) [CommRing A] [IsArtinianRing A] [IsReduced A] :
    IsRegularRing A := by
  refine isRegularRing_iff.mpr ?_
  intro p hp
  exact isRegularLocalRing_atPrime_of_artinian_reduced A p

/--
@isnad1 id=isregula.0h3v.s6.f5c9499ff882 from=translated src=- shape=21cf1940 vocab=2df2294a
-/
theorem isRegularLocalRing_localization_atPrime_of_formallyUnramified
    (k A : Type*) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FormallyUnramified k A] [Algebra.EssFiniteType k A]
    (p : Ideal A) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) := by
  have : Algebra.FormallyUnramified A (Localization.AtPrime p) :=
    Algebra.FormallyUnramified.of_isLocalization (Rₘ := Localization.AtPrime p) p.primeCompl
  have : Algebra.FormallyUnramified k (Localization.AtPrime p) :=
    Algebra.FormallyUnramified.comp k A (Localization.AtPrime p)
  have : Module.Finite k (Localization.AtPrime p) :=
    Algebra.FormallyUnramified.finite_of_free k (Localization.AtPrime p)
  have : IsArtinianRing (Localization.AtPrime p) :=
    IsArtinianRing.of_finite k (Localization.AtPrime p)
  have : IsReduced (Localization.AtPrime p) :=
    Algebra.FormallyUnramified.isReduced_of_field k (Localization.AtPrime p)
  exact isRegularLocalRing_of_isField _
    (IsArtinianRing.isField_of_isReduced_of_isLocalRing (Localization.AtPrime p))

/--
@isnad1 id=isregula.0h3v.s6.cea5d5f1a865 from=translated src=- shape=aff9a903 vocab=1fbbe4c3
-/
theorem isRegularLocalRing_localization_atPrime_of_etale
    (k A : Type*) [Field k] [CommRing A] [Algebra k A] [Algebra.Etale k A]
    (p : Ideal A) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) :=
  isRegularLocalRing_localization_atPrime_of_formallyUnramified k A p

/--
@isnad1 id=isregula.0h2v.s5.94885a3c6905 from=translated src=- shape=962998db vocab=29c8448b
-/
theorem isRegularRing_of_etale
    (k A : Type*) [Field k] [CommRing A] [Algebra k A] [Algebra.Etale k A] :
    IsRegularRing A := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  refine isRegularRing_iff.mpr ?_
  intro p hp
  exact isRegularLocalRing_localization_atPrime_of_etale k A p

/--
@isnad1 id=iff.0h0v.s6.55a109ee9de1 from=translated src=- shape=08c7faa3 vocab=ac5d1071
-/
theorem smoothFieldFiberRegularStalksInput_iff :
    SmoothFieldFiberRegularStalksInput.{u} ↔
      ∀ (k A : Type u) [Field k] [CommRing A] [Algebra k A],
        Algebra.Smooth k A → ∀ (p : Ideal A) [p.IsPrime],
          IsRegularLocalRing (Localization.AtPrime p) :=
  Iff.rfl

/--
@isnad1 id=isregula.1h2v.s5.6dd15e5ee27f from=translated src=- shape=bffd87ba vocab=6be36c2a
-/
theorem isRegularRing_of_smooth_of_input
    (hinput : SmoothFieldFiberRegularStalksInput.{u})
    (k A : Type u) [Field k] [CommRing A] [Algebra k A] [Algebra.Smooth k A] :
    IsRegularRing A := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  refine isRegularRing_iff.mpr ?_
  intro p hp
  exact hinput k A ‹Algebra.Smooth k A› p

/--
@isnad1 id=ne.0h1v.s6.5f5e6e4d140b from=translated src=- shape=bbb5e9b9 vocab=f44f2013
-/
theorem eps_ne_zero (K : Type*) [Field K] : (DualNumber.eps : DualNumber K) ≠ 0 := by
  intro heq
  have h1 := congrArg TrivSqZeroExt.snd heq
  exact one_ne_zero h1

/--
@isnad1 id=eq.0h1v.s7.cd9142ff8b68 from=translated src=- shape=729f92b7 vocab=c0c65631
-/
theorem nilradical_dualNumber_eq_span_eps (K : Type*) [Field K] :
    nilradical (DualNumber K) = Ideal.span {(DualNumber.eps : DualNumber K)} := by
  rcases DualNumber.ideal_trichotomy (nilradical (DualNumber K)) with h0 | h1 | h2
  · exfalso
    have hin : (DualNumber.eps : DualNumber K) ∈ nilradical (DualNumber K) :=
      mem_nilradical.mpr DualNumber.isNilpotent_eps
    rw [h0] at hin
    exact eps_ne_zero K (by simpa using hin)
  · exact h1
  · exfalso
    have hone : IsNilpotent (1 : DualNumber K) :=
      mem_nilradical.mp (h2 ▸ Submodule.mem_top)
    obtain ⟨n, hn⟩ := hone
    rw [one_pow] at hn
    exact one_ne_zero hn

/--
@isnad1 id=eq.0h1v.s5.a4dbab31f5c9 from=translated src=- shape=fe60498e vocab=1b1de9a2
-/
theorem ringKrullDim_dualNumber_eq_zero (K : Type*) [Field K] :
    ringKrullDim (DualNumber K) = 0 := by
  have : (nilradical (DualNumber K)).IsMaximal := by
    rw [nilradical_dualNumber_eq_span_eps K]
    exact DualNumber.isMaximal_span_singleton_eps
  have : Ring.KrullDimLE 0 (DualNumber K) :=
    Ring.KrullDimLE.of_isMaximal_nilradical (DualNumber K)
  exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance

/--
@isnad1 id=eq.0h1v.s7.0f0332ab22ff from=translated src=- shape=0dd4c6d6 vocab=977eaa47
-/
theorem spanFinrank_maximalIdeal_dualNumber_eq_one (K : Type*) [Field K] :
    (maximalIdeal (DualNumber K)).spanFinrank = 1 := by
  rw [DualNumber.maximalIdeal_eq_span_singleton_eps, ← Ideal.submodule_span_eq]
  exact Submodule.spanFinrank_singleton (eps_ne_zero K)

/--
@isnad1 id=not.0h1v.s5.0586f5315f50 from=translated src=- shape=fba248a8 vocab=122c3184
-/
theorem not_isRegularLocalRing_dualNumber (K : Type*) [Field K] :
    ¬ IsRegularLocalRing (DualNumber K) := by
  intro h
  have hspan := h.spanFinrank_maximalIdeal
  rw [ringKrullDim_dualNumber_eq_zero K, spanFinrank_maximalIdeal_dualNumber_eq_one K]
    at hspan
  have h10 : (1 : ℕ) = 0 := by exact_mod_cast hspan
  exact one_ne_zero h10

/--
@isnad1 id=isfield.0h1v.s4.94ee3857e90d from=translated src=- shape=90b7e236 vocab=af6a2a87
-/
theorem isField_of_isRegularLocalRing_of_krullDimLE_zero
    (R : Type*) [CommRing R] [Ring.KrullDimLE 0 R] [IsRegularLocalRing R] :
    IsField R := by
  have hspan := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
  rw [ringKrullDimZero_iff_ringKrullDim_eq_zero.mp ‹Ring.KrullDimLE 0 R›] at hspan
  have h0 : (maximalIdeal R).spanFinrank = 0 := by exact_mod_cast hspan
  exact IsLocalRing.isField_iff_maximalIdeal_eq.mpr
    ((Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).mp h0)

/--
@isnad1 id=not.0h1v.s8.daeeed165e8c from=translated src=- shape=025fa253 vocab=e1ba301c
-/
theorem not_isRegularLocalRing_localization_atPrime_dualNumber (K : Type*) [Field K] :
    ¬ IsRegularLocalRing (Localization.AtPrime (maximalIdeal (DualNumber K))) := by
  intro h
  have : IsNoetherianRing (DualNumber K) := PrincipalIdealRing.isNoetherianRing
  have : (nilradical (DualNumber K)).IsMaximal := by
    rw [nilradical_dualNumber_eq_span_eps K]
    exact DualNumber.isMaximal_span_singleton_eps
  have : Ring.KrullDimLE 0 (DualNumber K) :=
    Ring.KrullDimLE.of_isMaximal_nilradical (DualNumber K)
  have : IsArtinianRing (DualNumber K) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  have hf : IsField (Localization.AtPrime (maximalIdeal (DualNumber K))) :=
    isField_of_isRegularLocalRing_of_krullDimLE_zero
      (Localization.AtPrime (maximalIdeal (DualNumber K)))
  let := IsField.toField (R := Localization.AtPrime (maximalIdeal (DualNumber K))) hf
  have hz : algebraMap (DualNumber K)
      (Localization.AtPrime (maximalIdeal (DualNumber K))) DualNumber.eps = 0 :=
    (DualNumber.isNilpotent_eps.map (algebraMap (DualNumber K)
      (Localization.AtPrime (maximalIdeal (DualNumber K))))).eq_zero
  obtain ⟨⟨m, hm⟩, hm'⟩ := (IsLocalization.map_eq_zero_iff
    (maximalIdeal (DualNumber K)).primeCompl
    (Localization.AtPrime (maximalIdeal (DualNumber K))) DualNumber.eps).mp hz
  have hu : IsUnit m := by
    by_contra hnu
    exact hm ((IsLocalRing.mem_maximalIdeal m).mpr hnu)
  exact eps_ne_zero K (hu.mul_right_eq_zero.mp hm')

/--
@isnad1 id=not.0h0v.s6.af3ad268f56e from=translated src=- shape=d8111939 vocab=39684102
-/
theorem not_forall_regular_stalks_without_smooth :
    ¬ (∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] (p : Ideal A) [p.IsPrime],
        IsRegularLocalRing (Localization.AtPrime p)) := by
  intro hclaim
  exact not_isRegularLocalRing_localization_atPrime_dualNumber ℚ
    (hclaim ℚ (DualNumber ℚ) (maximalIdeal (DualNumber ℚ)))

end SmoothFieldFiberRegularStalks
