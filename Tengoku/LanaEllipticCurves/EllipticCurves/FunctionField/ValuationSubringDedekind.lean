/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.Seed.RingTheory.DedekindDomain.AdicValuation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Valuation subrings of the fraction field of a Dedekind domain

Let `R` be a Dedekind domain with fraction field `K`.  Mathlib attaches to every height-one prime
`v` of `R` the valuation subring `IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v`
— the localisation `R_v`, sitting inside `K` — and identifies it with the valuation subring of the
`v`-adic valuation.  This file proves the **converse**: those are *all* the valuation subrings of
`K` that contain `R`, apart from `K` itself.

```
IsDedekindDomain.exists_valuationSubringAtPrime_eq :
  (∀ r : R, algebraMap R K r ∈ O) → O ≠ ⊤ → ∃ v, valuationSubringAtPrime K v = O
```

Classically this is the statement that the places of `K` lying over the primes of `R` are exactly
the localisations of `R`, and it is the engine of the classification of the places of a function
field (Stichtenoth, *Algebraic Function Fields and Codes*, I.1.5–I.2.2).  The classical proof
argues that a discrete valuation ring is a *maximal* proper subring of its fraction field;
Mathlib's `ValuationSubring.eq_of_le_of_ne_top`, available under `[Ring.KrullDimLE 1 A]`, is that
statement, and `valuationSubringAtPrime` already carries the `Ring.KrullDimLE 1` instance.  So the
work here is only to produce the prime, which is the contraction of the maximal ideal of `O`.

## Main results

* `ValuationSubring.maximalIdeal_ne_bot` — a proper valuation subring of a field has a nonzero
  maximal ideal (equivalently: it is not a field);
* `ValuationSubring.mul_mem_nonunits` — the nonunits of `O`, viewed inside `K`, absorb
  multiplication by `O`;
* **`IsDedekindDomain.exists_valuationSubringAtPrime_eq`** — the classification above;
* `IsDedekindDomain.exists_valuationSubring_eq` — the same, phrased with
  `(v.valuation K).valuationSubring`;
* `IsDedekindDomain.exists_valuationSubringAtPrime_eq_iff` — the two hypotheses are not merely
  sufficient but *characterise* the valuation subrings of this form, via the converse lemmas
  `HeightOneSpectrum.algebraMap_mem_valuationSubringAtPrime` and
  `HeightOneSpectrum.valuationSubringAtPrime_ne_top`;
* **`HeightOneSpectrum.valuationSubringAtPrime_injective`** — `v ↦ R_v` is injective, so with the
  previous result it is a *bijection* from the height-one primes of `R` onto the proper valuation
  subrings of `K` containing `R`.  The prime is recovered from the subring by
  `HeightOneSpectrum.mem_asIdeal_iff_mem_nonunits`.

Nothing in this file mentions elliptic curves; it is an upstream candidate, and sits next to
`Mathlib/RingTheory/DedekindDomain/AdicValuation.lean`.

## Implementation notes

`ValuationSubring K` is the formalisation of "place of `K`" used throughout this development: a
ring automorphism of `K` carries valuation subrings to valuation subrings, which is exactly what a
classification of places is for, and it avoids quantifying over value groups.
-/

open IsDedekindDomain

namespace ValuationSubring

variable {K : Type*} [Field K]

/-- A valuation subring `O ≠ ⊤` of a field has a nonzero maximal ideal.  Indeed a valuation subring
that is a field is everything: if `x ∉ O` then `x⁻¹ ∈ O`, and inverting again returns `x`.
@isnad1 id=ne.1h2v.s8.05a038f7d929 from=translated src=- shape=1c471a84 vocab=805ac009
-/
theorem maximalIdeal_ne_bot {O : ValuationSubring K} (hO : O ≠ ⊤) :
    IsLocalRing.maximalIdeal O ≠ ⊥ := by
  obtain ⟨x, hx⟩ : ∃ x : K, x ∉ O := by
    by_contra h
    push Not at h
    exact hO (by ext y; simpa using h y)
  have hx0 : x ≠ 0 := fun h => hx (h ▸ O.zero_mem)
  have hinv : x⁻¹ ∈ O := (O.mem_or_inv_mem x).resolve_left hx
  refine fun h => ?_
  have hmem : (⟨x⁻¹, hinv⟩ : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    exact (ValuationSubring.mem_nonunits_iff_or O).2 (Or.inr (by simpa [hx0] using hx))
  rw [h, Ideal.mem_bot] at hmem
  exact hx0 (by simpa [inv_eq_zero] using congrArg (Subtype.val) hmem)

/-- `A.nonunits` absorbs multiplication by elements of `A`: it is the maximal ideal of `A`, viewed
inside `K`.  (`ValuationSubring.nonunits` is only a `NonUnitalSubring K`, so this does not come for
free from its algebraic structure.)
@isnad1 id=mem.2h4v.s7.0ac9bfa5e5f5 from=translated src=- shape=9639b463 vocab=f70636bf
-/
theorem mul_mem_nonunits {O : ValuationSubring K} {x y : K} (hx : x ∈ O.nonunits) (hy : y ∈ O) :
    x * y ∈ O.nonunits := by
  rw [O.mem_nonunits_iff] at hx ⊢
  calc O.valuation (x * y) = O.valuation x * O.valuation y := map_mul _ _ _
    _ ≤ O.valuation x * 1 := by gcongr; exact (O.valuation_le_one_iff y).2 hy
    _ = O.valuation x := mul_one _
    _ < 1 := hx

end ValuationSubring

namespace IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

namespace HeightOneSpectrum

variable (v : HeightOneSpectrum R)

/-- `R` is contained in the localisation of `R` at any height-one prime.
@isnad1 id=mem.0h4v.s6.7c90d3e3078f from=translated src=- shape=5014dc10 vocab=81255bf2
-/
theorem algebraMap_mem_valuationSubringAtPrime (r : R) :
    algebraMap R K r ∈ valuationSubringAtPrime K v :=
  ⟨r, 1, v.asIdeal.primeCompl.one_mem, by simp⟩

/-- The localisation of `R` at a height-one prime is a *proper* subring of `K`.
@isnad1 id=ne.0h3v.s6.5c1f7b6e9856 from=translated src=- shape=88424fa7 vocab=2c448787
-/
theorem valuationSubringAtPrime_ne_top : valuationSubringAtPrime K v ≠ ⊤ := by
  rw [valuationSubringAtPrime_eq_valuationSubring]
  simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]
  infer_instance

/-- **The prime is recoverable from the subring**: `v.asIdeal` is the contraction to `R` of the
nonunits of `R_v`.  This is the localisation fact `IsLocalization.AtPrime.to_map_mem_maximal_iff`,
read through `ValuationSubring.coe_mem_nonunits_iff`; the point of phrasing it with
`ValuationSubring.nonunits` rather than with `IsLocalRing.maximalIdeal` is that
`(valuationSubringAtPrime K v).nonunits` is a subset of `K` that depends on `v` *only through the
subring*, which is what makes `valuationSubringAtPrime_injective` a one-liner.
@isnad1 id=iff.0h4v.s7.e1eecf9525b8 from=translated src=- shape=fdb69afb vocab=deb18591
-/
theorem mem_asIdeal_iff_mem_nonunits (r : R) :
    r ∈ v.asIdeal ↔ algebraMap R K r ∈ (valuationSubringAtPrime K v).nonunits := by
  have hcoe : algebraMap R K r
      = ((algebraMap R (valuationSubringAtPrime K v) r : valuationSubringAtPrime K v) : K) := rfl
  rw [hcoe, ValuationSubring.coe_mem_nonunits_iff]
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ v.asIdeal r).symm

/-- **Distinct height-one primes give distinct valuation subrings.**  Together with
`exists_valuationSubringAtPrime_eq` this makes `v ↦ R_v` a bijection onto the proper valuation
subrings of `K` containing `R`.
@isnad1 id=injectiv.0h2v.s5.de731b481dac from=translated src=- shape=0f141560 vocab=002eb548
-/
theorem valuationSubringAtPrime_injective :
    Function.Injective (valuationSubringAtPrime K : HeightOneSpectrum R → ValuationSubring K) := by
  intro v w h
  refine HeightOneSpectrum.ext (Ideal.ext fun r => ?_)
  rw [mem_asIdeal_iff_mem_nonunits (K := K) v r, mem_asIdeal_iff_mem_nonunits (K := K) w r, h]

/--
@isnad1 id=iff.0h4v.s6.f00771425419 from=translated src=- shape=8e94b02e vocab=5553c6ec
-/
@[simp]
theorem valuationSubringAtPrime_inj {v w : HeightOneSpectrum R} :
    valuationSubringAtPrime K v = valuationSubringAtPrime K w ↔ v = w :=
  valuationSubringAtPrime_injective.eq_iff

end HeightOneSpectrum

/-- **Every proper valuation subring of `K` containing a Dedekind domain `R` with `Frac R = K` is
the localisation of `R` at a height-one prime.**

The prime is the contraction to `R` of the maximal ideal of `O`; it is nonzero because clearing the
denominator of a nonzero element of that maximal ideal produces a nonzero element of `R` inside it.
Once `R_v ≤ O` is known, `ValuationSubring.eq_of_le_of_ne_top` upgrades it to equality, since `R_v`
has Krull dimension at most one.
@isnad1 id=ex.2h3v.s7.8f21e3939ba8 from=translated src=- shape=101f9da8 vocab=1f1c21e8
-/
theorem exists_valuationSubringAtPrime_eq (O : ValuationSubring K)
    (hR : ∀ r : R, algebraMap R K r ∈ O) (hO : O ≠ ⊤) :
    ∃ v : HeightOneSpectrum R, HeightOneSpectrum.valuationSubringAtPrime K v = O := by
  set φ : R →+* O := (algebraMap R K).codRestrict O hR with hφ
  have hcoe : ∀ r : R, ((φ r : O) : K) = algebraMap R K r := fun _ => rfl
  set p : Ideal R := Ideal.comap φ (IsLocalRing.maximalIdeal O) with hp
  haveI hprime : p.IsPrime := Ideal.comap_isPrime φ _
  -- the prime is nonzero: clear the denominator of a nonzero element of the maximal ideal
  obtain ⟨z, hzm, hz0⟩ := Submodule.ne_bot_iff _ |>.1 (ValuationSubring.maximalIdeal_ne_bot hO)
  obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors R) ((z : O) : K)
  have hdne : algebraMap R K (d : R) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
  have hzne : ((z : O) : K) ≠ 0 := fun h => hz0 (Subtype.ext h)
  have hnmem : n ∈ p := by
    have hφn : φ n = z * φ (d : R) := by
      apply Subtype.ext
      simpa [hcoe] using hnd.symm
    rw [hp, Ideal.mem_comap, hφn]
    exact Ideal.mul_mem_right _ _ hzm
  have hn0 : n ≠ 0 := by
    intro h
    apply hzne
    have hmul : ((z : O) : K) * algebraMap R K (d : R) = 0 := by rw [hnd, h, map_zero]
    exact (mul_eq_zero.1 hmul).resolve_right hdne
  have hpne : p ≠ ⊥ := fun h => hn0 (by simpa [h, Ideal.mem_bot] using hnmem)
  -- the localisation of `R` at that prime is contained in `O`, hence equal to it
  refine ⟨⟨p, hprime, hpne⟩, ValuationSubring.eq_of_le_of_ne_top _ ?_ hO⟩
  rintro x ⟨a, s, hs, rfl⟩
  have hunit : IsUnit (φ s) := by
    by_contra h
    exact hs ((Ideal.mem_comap).2 ((IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 h)))
  obtain ⟨u, hu⟩ := hunit
  have hmul : algebraMap R K s * ((↑u⁻¹ : O) : K) = 1 := by
    rw [← hcoe s, ← hu]
    exact_mod_cast u.mul_inv
  rw [inv_eq_of_mul_eq_one_right hmul]
  exact mul_mem (hR a) (SetLike.coe_mem _)

/-- The form of `exists_valuationSubringAtPrime_eq` phrased with the `v`-adic valuation.
@isnad1 id=ex.2h3v.s7.418042a06a65 from=translated src=- shape=4cf2dba5 vocab=707bf178
-/
theorem exists_valuationSubring_eq (O : ValuationSubring K)
    (hR : ∀ r : R, algebraMap R K r ∈ O) (hO : O ≠ ⊤) :
    ∃ v : HeightOneSpectrum R, (v.valuation K).valuationSubring = O := by
  obtain ⟨v, hv⟩ := exists_valuationSubringAtPrime_eq O hR hO
  exact ⟨v, by rwa [← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]⟩

/-- Containing `R` and being proper *characterise* the valuation subrings of `K` of the form
`R_v`: the two hypotheses of `exists_valuationSubringAtPrime_eq` are also necessary.
@isnad1 id=iff.0h3v.s7.15c0f58aa0ed from=translated src=- shape=1024c698 vocab=1f1c21e8
-/
theorem exists_valuationSubringAtPrime_eq_iff (O : ValuationSubring K) :
    (∃ v : HeightOneSpectrum R, HeightOneSpectrum.valuationSubringAtPrime K v = O) ↔
      (∀ r : R, algebraMap R K r ∈ O) ∧ O ≠ ⊤ := by
  refine ⟨?_, fun h => exists_valuationSubringAtPrime_eq O h.1 h.2⟩
  rintro ⟨v, rfl⟩
  exact ⟨fun r => HeightOneSpectrum.algebraMap_mem_valuationSubringAtPrime v r,
    HeightOneSpectrum.valuationSubringAtPrime_ne_top v⟩

end IsDedekindDomain
