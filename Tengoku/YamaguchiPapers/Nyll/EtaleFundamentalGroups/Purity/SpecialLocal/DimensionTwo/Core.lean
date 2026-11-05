/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.SchemeTheory.RingTheory.Ramification.Trace.FiniteFreeDiscriminant
import Tengoku.Seed.RingTheory.Ideal.KrullsHeightTheorem
import Tengoku.Seed.RingTheory.Localization.NormTrace
import Tengoku.Seed.RingTheory.Regular.RegularSequence
import Tengoku.Seed.RingTheory.Smooth.Fiber

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Dimension-two purity for finite free algebras

For a finite free algebra, formal unramifiedness is detected by the trace
discriminant.  Over a Noetherian domain, a nonzero element whose image is a
unit at every height-one localization is already a unit: otherwise a minimal
prime over its principal ideal gives a height-one point where its image lies
in the maximal ideal.

A regular pair generating the maximal ideal supplies a height-one prime, so
the discriminant cannot vanish.  Consequently, if every height-one
localization of a finite free algebra is etale, its global discriminant is a
unit and the algebra is etale over the base.
-/

noncomputable section

namespace EtaleFundamentalGroups.SpecialLocalPurity

open IsLocalRing Module
open RingTheory.Sequence

universe u v

/-- A nonzero nonunit in a Noetherian domain is contained in a height-one
prime.  The prime is chosen minimal over the element's principal ideal.-/
theorem exists_height_one_prime_containing_of_nonzero_nonunit
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {d : A} (hd : d ≠ 0) (hdu : ¬ IsUnit d) :
    ∃ p : Ideal A, p.IsPrime ∧ p.height = 1 ∧ d ∈ p := by
  obtain ⟨p, hpMin⟩ :=
    (Ideal.span ({d} : Set A)).nonempty_minimalPrimes (by simpa)
  have hpNe : p ≠ ⊥ := by
    intro hp
    apply hd
    apply Ideal.span_singleton_eq_bot.mp
    exact bot_unique (hpMin.le.trans_eq hp)
  have hpHeight : p.height = 1 := by
    let : p.IsPrime := hpMin.isPrime
    apply le_antisymm
    · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
        (Ideal.span ({d} : Set A)) p hpMin
    · exact (Order.one_le_iff_ne_zero.mpr
        (Ideal.height_eq_zero_iff_eq_bot.not.mpr hpNe))
  exact ⟨p, hpMin.isPrime, hpHeight,
    hpMin.le (Ideal.mem_span_singleton_self d)⟩

/-- In a Noetherian domain, a nonzero element which becomes a unit at
every height-one localization is a unit.-/
theorem isUnit_of_isUnit_localizationAtPrime_height_one
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {d : A} (hd : d ≠ 0)
    (hlocal : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 →
      IsUnit (algebraMap A (Localization.AtPrime p) d)) :
    IsUnit d := by
  by_contra hdu
  obtain ⟨p, hpPrime, hpHeight, hdMem⟩ :=
    exists_height_one_prime_containing_of_nonzero_nonunit hd hdu
  let : p.IsPrime := hpPrime
  have hdUnit := hlocal p hpHeight
  have hdLocalMem : algebraMap A (Localization.AtPrime p) d ∈
      maximalIdeal (Localization.AtPrime p) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (Localization.AtPrime p) p d).mpr hdMem
  have hdNotUnit : ¬ IsUnit (algebraMap A (Localization.AtPrime p) d) := by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hdLocalMem
  exact hdNotUnit hdUnit

/-- A regular pair generating the maximal ideal of a Noetherian local
domain produces a height-one prime.-/
theorem exists_height_one_prime_of_regular_pair
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A]
    {x y : A} (hregular : IsRegular A [x, y])
    (hspan : Ideal.ofList [x, y] = maximalIdeal A) :
    ∃ p : Ideal A, p.IsPrime ∧ p.height = 1 := by
  have hxRegular : IsSMulRegular A x :=
    ((isRegular_cons_iff A x [y]).mp hregular).1
  have hx : x ≠ 0 := by
    intro hx
    exact one_ne_zero (hxRegular.right_eq_zero_of_smul (by simp [hx]))
  have hxMem : x ∈ maximalIdeal A := by
    rw [← hspan]
    exact Ideal.subset_span List.mem_cons_self
  have hxNotUnit : ¬ IsUnit x := by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hxMem
  obtain ⟨p, hpPrime, hpHeight, -⟩ :=
    exists_height_one_prime_containing_of_nonzero_nonunit hx hxNotUnit
  exact ⟨p, hpPrime, hpHeight⟩

end EtaleFundamentalGroups.SpecialLocalPurity

end
