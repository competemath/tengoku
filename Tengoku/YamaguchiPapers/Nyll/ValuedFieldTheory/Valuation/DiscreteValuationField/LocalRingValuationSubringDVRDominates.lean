/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Tengoku.Seed.Algebra.Algebra.Basic
import Tengoku.Seed.Algebra.Algebra.Subalgebra.Basic
import Tengoku.Seed.Algebra.Algebra.Tower
import Tengoku.Seed.Data.Finset.Max
import Tengoku.Seed.Algebra.Algebra.Subalgebra.Lattice
import Tengoku.Seed.RingTheory.Adjoin.FG
import Tengoku.Seed.RingTheory.DedekindDomain.Basic
import Tengoku.Seed.RingTheory.DedekindDomain.AdicValuation
import Tengoku.Seed.RingTheory.DedekindDomain.Dvr
import Tengoku.Seed.RingTheory.FiniteType
import Tengoku.Seed.RingTheory.Ideal.GoingUp
import Tengoku.Seed.RingTheory.Ideal.Height
import Tengoku.Seed.RingTheory.Ideal.KrullsHeightTheorem
import Tengoku.Seed.RingTheory.Ideal.Maps
import Tengoku.Seed.RingTheory.Ideal.Maximal
import Tengoku.Seed.RingTheory.Ideal.MinimalPrime.Basic
import Tengoku.Seed.RingTheory.Ideal.Over
import Tengoku.Seed.RingTheory.Ideal.Span
import Tengoku.Seed.RingTheory.IntegralClosure.IntegrallyClosed
import Tengoku.Seed.RingTheory.LocalRing.LocalSubring
import Tengoku.Seed.RingTheory.LocalRing.MaximalIdeal.Basic
import Tengoku.Seed.RingTheory.Localization.AtPrime.Basic
import Tengoku.Seed.RingTheory.Localization.FractionRing
import Tengoku.Seed.RingTheory.Localization.Integral
import Tengoku.Seed.RingTheory.Localization.LocalizationLocalization
import Tengoku.Seed.RingTheory.Localization.Submodule
import Tengoku.Seed.RingTheory.Noetherian.Defs
import Tengoku.Seed.RingTheory.Valuation.Basic
import Tengoku.Seed.RingTheory.Valuation.LocalSubring
import Tengoku.Seed.RingTheory.Valuation.ValuationSubring
import Tengoku.Seed.Tactic.Ext
import Tengoku.Seed.Tactic.NormNum.Basic
import Tengoku.Seed.Tactic.Push
import Tengoku.Seed.Tactic.Set
import Tengoku.YamaguchiPapers.Nyll.SchemeTheory.RingTheory.Dimension.NoetherianRingKrullDimensionLeOne

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Discrete valuation rings dominating noetherian local domains

This file constructs a height-one prime in a finitely generated subalgebra of the fraction field
and uses its integral closure to obtain a discrete valuation ring dominating the local domain.
-/

section ProofImplementation

namespace AlgebraicCurves.Valuations.Proofs
namespace IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates

universe u v

open IsLocalRing

namespace DvrDomination

/--
@isnad1 id=dimensio.1h1v.s5.640caddac493 from=translated src=- shape=50208249 vocab=4c899cc1
-/
theorem dimensionLEOne_of_ringKrullDim_le_one (C : Type u) [CommRing C] [IsDomain C]
    (h : ringKrullDim C ≤ 1) : Ring.DimensionLEOne C := by
  refine Ring.DimensionLEOne.mk (fun {p} hp0 hp => ?_)
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p hp.ne_top
  by_contra hnot
  have hlt : p < m := lt_of_le_of_ne hpm (fun h => hnot (h ▸ hm))
  have hbot : (⊥ : Ideal C) < p := bot_lt_iff_ne_bot.mpr hp0
  have := hm.isPrime
  have h1 : (⊥ : Ideal C).height + 1 ≤ p.height := Ideal.height_add_one_le_of_lt_of_isPrime hbot
  have h2 : p.height + 1 ≤ m.height := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h3 : (m.height : WithBot ℕ∞) ≤ ringKrullDim C :=
    Ideal.height_le_ringKrullDim_of_ne_top hm.ne_top
  rw [Ideal.height_bot, zero_add] at h1
  have h4 : (2 : ℕ∞) ≤ m.height := by
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ p.height + 1 := add_le_add h1 le_rfl
      _ ≤ m.height := h2
  have h5 : ((2 : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim C := le_trans (by exact_mod_cast h4) h3
  have h6 : ((2 : ℕ∞) : WithBot ℕ∞) ≤ 1 := le_trans h5 h
  exact absurd h6 (by decide)

section StepB

variable {K : Type v} [Field K]

end StepB

section StepA

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
variable {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] in
/--
@isnad1 id=ex.1h2v.s10.1746f008c0c4 from=translated src=- shape=b67a9e8e vocab=322ad151
-/
theorem exists_subalgebra_prime_height_le_one (hR : ¬ IsField R) :
    ∃ (S : Subalgebra R K) (P : Ideal ↥S) (_ : P.IsPrime),
      IsNoetherianRing ↥S ∧ P ≠ ⊥ ∧ P.height ≤ 1 ∧
      ∀ r : R, r ∈ maximalIdeal R ↔ algebraMap R ↥S r ∈ P := by
  classical
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  obtain ⟨V₀, hV₀⟩ := (LocalSubring.range (algebraMap R K)).exists_le_valuationSubring
  obtain ⟨hle, hloc⟩ := LocalSubring.le_def.mp hV₀
  have hRV : ∀ r : R, algebraMap R K r ∈ V₀ := by
    intro r
    have : algebraMap R K r ∈ (LocalSubring.range (algebraMap R K)).toSubring := by
      rw [LocalSubring.range_toSubring]; exact ⟨r, rfl⟩
    exact hle this
  have hrange : ∀ z : K, z ∈ (LocalSubring.range (algebraMap R K)).toSubring ↔
      z ∈ Set.range (algebraMap R K) := by
    intro z; rw [LocalSubring.range_toSubring]; rfl
  have hunitV : ∀ r : R, r ∉ maximalIdeal R → V₀.valuation (algebraMap R K r) = 1 := by
    intro r hr
    have hu : IsUnit r := by
      by_contra h; exact hr ((IsLocalRing.mem_maximalIdeal _).mpr h)
    have : IsUnit (⟨algebraMap R K r, hRV r⟩ : ↥V₀) :=
      hu.map ((algebraMap R K).codRestrict V₀ hRV)
    exact (V₀.valuation_eq_one_iff ⟨algebraMap R K r, hRV r⟩).mp this
  have hdomV : ∀ r : R, r ∈ maximalIdeal R → V₀.valuation (algebraMap R K r) < 1 := by
    intro r hr
    have hle1 : V₀.valuation (algebraMap R K r) ≤ 1 := (V₀.valuation_le_one_iff _).mpr (hRV r)
    rcases hle1.lt_or_eq with hlt | heq
    · exact hlt
    exfalso
    have hmemA : algebraMap R K r ∈ (LocalSubring.range (algebraMap R K)).toSubring :=
      (hrange _).mpr ⟨r, rfl⟩
    have huV : IsUnit (Subring.inclusion hle ⟨algebraMap R K r, hmemA⟩) :=
      (V₀.valuation_eq_one_iff ⟨algebraMap R K r, hRV r⟩).mpr heq
    have huA :
        IsUnit (⟨algebraMap R K r, hmemA⟩ : ↥(LocalSubring.range (algebraMap R K)).toSubring) :=
      hloc.map_nonunit _ huV
    obtain ⟨⟨a, b, hab, hba⟩, ha⟩ := huA
    have ha' : (a : K) = algebraMap R K r := congrArg Subtype.val ha
    obtain ⟨r', hr'⟩ := (hrange _).mp b.2
    have hmul : algebraMap R K (r * r') = algebraMap R K 1 := by
      rw [map_mul, map_one, ← ha', hr']
      exact congrArg Subtype.val hab
    have hunit : IsUnit r := IsUnit.of_mul_eq_one r' (hinj hmul)
    exact (IsLocalRing.mem_maximalIdeal _).mp hr hunit
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (maximalIdeal R) : (maximalIdeal R).FG)
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply hR
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← hs, Finset.coe_empty, Submodule.span_empty]
  obtain ⟨x, hxs, hxmax⟩ := s.exists_max_image (fun y => V₀.valuation (algebraMap R K y)) hsne
  have hsm : ∀ y ∈ s, y ∈ maximalIdeal R := fun y hy => hs ▸ Ideal.subset_span hy
  have hx0 : algebraMap R K x ≠ 0 := by
    intro h0
    obtain ⟨y, hys, hy0⟩ : ∃ y ∈ s, y ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hR
      rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← hs, Ideal.span_eq_bot]
      exact hall
    have := hxmax y hys
    rw [h0, map_zero] at this
    exact (map_ne_zero_iff _ hinj).mpr hy0 ((Valuation.zero_iff _).mp (le_zero_iff.mp this))
  set T : Finset K := s.image (fun y => algebraMap R K y / algebraMap R K x) with hT
  set S : Subalgebra R K := Algebra.adjoin R (T : Set K) with hS
  have hSnoeth : IsNoetherianRing ↥S := by
    have : Algebra.FiniteType R ↥S :=
      (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset T)
    exact Algebra.FiniteType.isNoetherianRing R ↥S
  let V₀' : Subalgebra R K :=
    { V₀.toSubring with algebraMap_mem' := fun r => hRV r }
  have hSV : S ≤ V₀' := by
    rw [hS]
    refine Algebra.adjoin_le ?_
    intro t ht
    rw [hT, Finset.coe_image] at ht
    obtain ⟨y, hy, rfl⟩ := ht
    change algebraMap R K y / algebraMap R K x ∈ V₀
    rw [← V₀.valuation_le_one_iff, map_div₀, div_le_one₀ (by
      rw [Valuation.pos_iff]; exact hx0)]
    exact hxmax y hy
  have hSV' : ∀ z : ↥S, (z : K) ∈ V₀ := fun z => hSV z.2
  let x' : ↥S := ⟨algebraMap R K x, Subalgebra.algebraMap_mem S x⟩
  have hx'0 : x' ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  let toV : ↥S →+* ↥V₀ :=
    { toFun := fun z => ⟨z, hSV' z⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  let 𝔮 : Ideal ↥S := (maximalIdeal ↥V₀).comap toV
  have h𝔮 : 𝔮.IsPrime := Ideal.comap_isPrime toV _
  have hx'𝔮 : x' ∈ 𝔮 := by
    change toV x' ∈ maximalIdeal ↥V₀
    rw [ValuationSubring.valuation_lt_one_iff]
    exact hdomV x (hsm x hxs)
  obtain ⟨P, hPmin, hP𝔮⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {x'}) (J := 𝔮)
    ((Ideal.span_singleton_le_iff_mem _).mpr hx'𝔮)
  have hPprime : P.IsPrime := hPmin.1.1
  have hxP : x' ∈ P := hPmin.1.2 (Ideal.mem_span_singleton_self x')
  refine ⟨S, P, hPprime, hSnoeth, ?_, ?_, ?_⟩
  · intro h; rw [h] at hxP; exact hx'0 ((Submodule.mem_bot _).mp hxP)
  · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {x'}) P hPmin
  · intro r
    constructor
    · intro hr
      apply hPmin.1.2
      have hmap : Ideal.map (algebraMap R ↥S) (maximalIdeal R) ≤ Ideal.span {x'} := by
        rw [← hs, Ideal.map_span]
        refine Ideal.span_le.mpr ?_
        rintro z ⟨y, hy, rfl⟩
        rw [SetLike.mem_coe, Ideal.mem_span_singleton']
        refine ⟨⟨algebraMap R K y / algebraMap R K x, ?_⟩, ?_⟩
        · rw [hS]; exact Algebra.subset_adjoin (by rw [hT, Finset.coe_image]; exact ⟨y, hy, rfl⟩)
        · apply Subtype.ext
          change algebraMap R K y / algebraMap R K x * algebraMap R K x = (algebraMap R ↥S y : K)
          rw [div_mul_cancel₀ _ hx0]
          rfl
      exact hmap (Ideal.mem_map_of_mem _ hr)
    · intro hr
      by_contra hnot
      have h1 := hunitV r hnot
      have h2 : toV (algebraMap R ↥S r) ∈ maximalIdeal ↥V₀ := hP𝔮 hr
      rw [ValuationSubring.valuation_lt_one_iff] at h2
      change V₀.valuation (algebraMap R K r) < 1 at h2
      rw [h1] at h2
      exact lt_irrefl _ h2

end StepA

end DvrDomination

end IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates
end AlgebraicCurves.Valuations.Proofs
end ProofImplementation
