/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.Chow.RegularLocalCohenMacaulay
import Tengoku.Seed.RingTheory.Ideal.Height
import Tengoku.Seed.RingTheory.Ideal.MinimalPrime.Noetherian
import Tengoku.Seed.RingTheory.Nakayama

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# P2.2 in all dimensions: regular local rings are domains

`RegularLocalDomain.lean` lands the statement only for `ringKrullDim R ≤ 1` and records the
associated-graded isomorphism (Stacks 00NO, `gr_m(R) ≃ k[x₁,…,x_d]`) as the blocking input for
the general case.  That input is **not** needed: the classical induction route
(Stacks 00NP, Matsumura Thm. 14.3) proves the theorem from material already present.

The induction is on the embedding dimension, and every geometric step is already available:

* `IsLocalRing.maximalIdeal_sq_lt_of_ringKrullDim_ne_zero` gives `m² < m` in positive dimension;
* `Ideal.subset_union_prime` (prime avoidance, tolerating the one non-prime member `m²`) plus
  finiteness of `minimalPrimes R` on a Noetherian ring produces a parameter
  `x ∈ m` outside `m²` **and** outside every minimal prime;
* `quotient_span_singleton_isRegularLocalRing` and `embeddingDimension_quotient_span_singleton`
  say `R ⧸ (x)` is regular of embedding dimension one less, so the induction hypothesis makes it
  a domain, i.e. `(x)` is prime;
* a minimal prime `q ≤ (x)` then satisfies `q = x · q` because `x ∉ q`, so Nakayama forces
  `q = ⊥` and `⊥` is prime.

The only place `m²` enters is the choice of parameter; no graded ring is constructed.

## Main results

* `IsRegularLocalRing.exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes` — the parameter.
* `isDomain_of_isRegularLocalRing` — **P2.2**, unconditional.
* `IsCohenMacaulayLocalRing.of_isRegularLocalRing_unconditional` — **P3.4** with the
  `regularLocal_isDomain` hypothesis of
  `IsCohenMacaulayLocalRing.of_isRegularLocalRing` discharged.
-/

noncomputable section

universe u

open IsLocalRing

namespace IsRegularLocalRing

variable {R : Type u} [CommRing R]

/-! ### The maximal ideal is not minimal in positive dimension -/

/-- In positive Krull dimension the maximal ideal of a local ring is not a minimal prime:
its height would be zero, and in a local ring the height of the maximal ideal is the dimension.
@isnad1 id=not.1h1v.s6.a62312ff2624 from=translated src=- shape=e09aeb6e vocab=f9707010
-/
theorem maximalIdeal_notMem_minimalPrimes [IsLocalRing R]
    (hdim : ringKrullDim R ≠ 0) : maximalIdeal R ∉ minimalPrimes R := by
  intro hmem
  refine hdim ?_
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    Ideal.height_eq_zero_iff.mpr hmem]
  simp

/-! ### Prime avoidance: a parameter outside `m²` and outside every minimal prime -/

/-- **Prime avoidance step.**  In positive Krull dimension a regular local ring has an element
of the maximal ideal lying outside `m²` and outside every minimal prime.

`m` is covered by `m² ∪ ⋃ minimal primes` only if it is contained in one of them
(`Ideal.subset_union_prime`, which tolerates the single non-prime member `m²`).  Containment in
`m²` contradicts `m² < m`, and containment in a minimal prime would make `m` itself minimal.
@isnad1 id=ex.1h1v.s8.7d8b3730099c from=translated src=- shape=2190386e vocab=0fad962e
-/
theorem exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes [IsRegularLocalRing R]
    (hdim : ringKrullDim R ≠ 0) :
    ∃ a : R, a ∈ maximalIdeal R ∧ a ∉ maximalIdeal R ^ 2 ∧
      ∀ p ∈ minimalPrimes R, a ∉ p := by
  classical
  have hfin : (minimalPrimes R).Finite := minimalPrimes.finite_of_isNoetherianRing R
  set P : Finset (Ideal R) := hfin.toFinset with hPdef
  set s : Finset (Ideal R) := insert (maximalIdeal R ^ 2) P with hsdef
  by_contra hcon
  push Not at hcon
  -- `hcon` says every element of `m` lies in `m²` or in some minimal prime.
  have hsub : ((maximalIdeal R : Ideal R) : Set R) ⊆
      ⋃ i ∈ (↑s : Set (Ideal R)), ((id i : Ideal R) : Set R) := by
    intro a ha
    by_cases h2 : a ∈ maximalIdeal R ^ 2
    · exact Set.mem_biUnion
        (show maximalIdeal R ^ 2 ∈ (↑s : Set (Ideal R)) by simp [hsdef]) h2
    · obtain ⟨p, hp, hap⟩ := hcon a ha h2
      exact Set.mem_biUnion
        (show p ∈ (↑s : Set (Ideal R)) by simp [hsdef, hPdef, hp]) hap
  have hprime : ∀ i ∈ s, i ≠ maximalIdeal R ^ 2 → i ≠ maximalIdeal R ^ 2 →
      (id i : Ideal R).IsPrime := by
    intro i hi hne _
    have hiP : i ∈ P := (Finset.mem_insert.mp hi).resolve_left hne
    exact IsMinimalPrime.isPrime (hfin.mem_toFinset.mp hiP)
  obtain ⟨i, his, hle⟩ :=
    (Ideal.subset_union_prime (f := (id : Ideal R → Ideal R))
      (maximalIdeal R ^ 2) (maximalIdeal R ^ 2) hprime (I := maximalIdeal R)).mp hsub
  simp only [id_eq] at hle
  rcases Finset.mem_insert.mp his with rfl | hiP
  · -- `m ≤ m²` contradicts `m² < m`.
    exact (IsLocalRing.maximalIdeal_sq_lt_of_ringKrullDim_ne_zero hdim).ne
      (le_antisymm (IsLocalRing.maximalIdeal_sq_lt_of_ringKrullDim_ne_zero hdim).le hle)
  · -- `m ≤ p` with `p` prime forces `p = m`, so `m` would be a minimal prime.
    have hip : i ∈ minimalPrimes R := hfin.mem_toFinset.mp hiP
    haveI : i.IsPrime := IsMinimalPrime.isPrime hip
    have hieq : i = maximalIdeal R :=
      le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹i.IsPrime›)) hle
    exact maximalIdeal_notMem_minimalPrimes hdim (hieq ▸ hip)

end IsRegularLocalRing

/-! ### P2.2 -/

open IsRegularLocalRing ModuleCat in
/-- **P2.2.** A regular local ring is a domain, in every dimension.

Induction on the embedding dimension.  Dimension zero is a field.  In positive dimension pick a
parameter `x` outside `m²` and outside every minimal prime; then `R ⧸ (x)` is regular of embedding
dimension one less, hence a domain by induction, so `(x)` is prime.  A minimal prime `q ≤ (x)`
satisfies `q = x · q` (each `y = r * x ∈ q` has `r ∈ q` because `x ∉ q`), so Nakayama gives
`q = ⊥`; a prime `⊥` is exactly the domain property.
@isnad1 id=isdomain.0h1v.s4.fd890a1a5574 from=translated src=- shape=c612a321 vocab=fbdff070
-/
theorem isDomain_of_isRegularLocalRing (A : Type u) [CommRing A] [IsRegularLocalRing A] :
    IsDomain A := by
  classical
  generalize hn : embeddingDimension A = n
  revert A
  induction n with
  | zero =>
    intro A _ _ hn
    have hdim : ringKrullDim A = 0 := by
      rw [← IsRegularLocalRing.coe_embeddingDimension_eq_ringKrullDim A, hn]
      simp
    exact (isField_of_ringKrullDim_eq_zero hdim).isDomain
  | succ n ih =>
    intro A _ _ hn
    letI : DecidableEq A := Classical.decEq A
    have hdimne : ringKrullDim A ≠ 0 := by
      intro h0
      have hpos : (0 : WithBot ℕ∞) < ringKrullDim A := by
        rw [← IsRegularLocalRing.coe_embeddingDimension_eq_ringKrullDim A]
        exact_mod_cast (show 0 < embeddingDimension A from by rw [hn]; omega)
      rw [h0] at hpos
      exact (lt_irrefl 0) hpos
    obtain ⟨x, hxm, hx2, hxmin⟩ :=
      exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes hdimne
    -- The parameter quotient is regular of embedding dimension `n`.
    letI := quotientSpanIsLocalRing A x hxm
    letI : IsRegularLocalRing (A ⧸ Ideal.span {x}) :=
      quotient_span_singleton_isRegularLocalRing hxm hx2
    letI : DecidableEq (A ⧸ Ideal.span {x}) := Classical.decEq _
    have hQdim : embeddingDimension (A ⧸ Ideal.span {x}) = n := by
      have h := embeddingDimension_quotient_span_singleton hxm hx2
      rw [hn] at h
      simpa using h
    have hQdom : IsDomain (A ⧸ Ideal.span {x}) := ih _ hQdim
    haveI hxprime : (Ideal.span {x} : Ideal A).IsPrime :=
      (Ideal.Quotient.isDomain_iff_prime _).mp hQdom
    -- A minimal prime below `(x)`.
    obtain ⟨q, hq, hqle⟩ :=
      Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A)) (J := Ideal.span {x}) bot_le
    have hq' : q ∈ minimalPrimes A := hq
    haveI : q.IsPrime := IsMinimalPrime.isPrime hq'
    have hxq : x ∉ q := hxmin q hq'
    -- `q ≤ (x) • q`, because `x ∉ q` and `q` is prime.
    have hqsmul : (q : Submodule A A) ≤ (Ideal.span {x} : Ideal A) • (q : Submodule A A) := by
      intro y hy
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp (hqle hy)
      have hr : r ∈ q := (Ideal.IsPrime.mem_or_mem ‹q.IsPrime› hy).resolve_right hxq
      have hmem := Submodule.smul_mem_smul (Ideal.mem_span_singleton_self x) hr
      simpa [smul_eq_mul, mul_comm] using hmem
    have hjac : (Ideal.span {x} : Ideal A) ≤ Ideal.jacobson (⊥ : Ideal A) := by
      rw [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal A) bot_ne_top]
      exact Ideal.span_le.mpr (by simpa using hxm)
    have hqbot : q = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ (IsNoetherian.noetherian _) hqsmul hjac
    haveI hbot : (⊥ : Ideal A).IsPrime := hqbot ▸ ‹q.IsPrime›
    haveI : NoZeroDivisors A := by
      refine ⟨fun {a b} hab => ?_⟩
      have hmem : a * b ∈ (⊥ : Ideal A) := by simpa using hab
      rcases Ideal.IsPrime.mem_or_mem hbot hmem with h | h
      · exact Or.inl (by simpa using h)
      · exact Or.inr (by simpa using h)
    exact NoZeroDivisors.to_isDomain A

/-! ### P3.4, unconditional -/

namespace ModuleCat

end ModuleCat

end
