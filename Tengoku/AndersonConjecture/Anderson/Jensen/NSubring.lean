/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku

/-!
# N-subrings and A-extensions

An N-subring of a complete local domain (T, M) is a quasi-local
UFD subring satisfying a height condition on associated primes.
An A-extension preserves primality and cardinality bounds.

* Heitmann, "Characterization of completions of UFDs", 1993.
* Jensen, "Completions of UFDs with semi-local formal fibers", 2006.
-/

noncomputable section

open Cardinal Ideal

/-!
## N-subring definition

For T a complete local domain, the N-subring conditions simplify:
- Condition (2) (Q ∩ R = (0) for Q ∈ Ass(T)) is automatic since
  Ass(T) = {(0)} and R ⊆ T domain.
- Condition (3): for every regular t ∈ T and P ∈ Ass(T/tT), ht(P ∩ R) ≤ 1.
-/

variable {T : Type*} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]

/-- An N-subring of a complete local domain (T, M).
This is a quasi-local UFD R ⊆ T with bounded cardinality and a height condition
on associated primes of principal ideals. -/
structure NSubring (T : Type*) [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T] where
  /-- The underlying subring of T -/
  carrier : Subring T
  /-- R is a UFD -/
  isUFD : UniqueFactorizationMonoid carrier
  /-- R is a local ring (quasi-local with M ∩ R as maximal ideal) -/
  isLocalRing : IsLocalRing carrier
  /-- |R| ≤ max(ℵ₀, |T/M|) -/
  card_le : Cardinal.mk carrier ≤ max Cardinal.aleph0 (Cardinal.mk (IsLocalRing.ResidueField T))
  /-- The maximal ideal of R equals the contraction of M to R.
  This ensures R is "centered on M" — prime elements of R land in M. -/
  maximal_ideal_eq : IsLocalRing.maximalIdeal carrier =
    (IsLocalRing.maximalIdeal T).comap carrier.subtype
  /-- For every nonzero t ∈ T and P ∈ Ass(T/tT), ht(P ∩ R) ≤ 1.
  This is the key condition ensuring that primes of T interact well with R. -/
  height_bound : ∀ (t : T), t ≠ 0 →
    ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {t}),
      Ideal.height (P.comap carrier.subtype) ≤ 1

namespace NSubring

instance (N : NSubring T) : UniqueFactorizationMonoid N.carrier := N.isUFD
instance (N : NSubring T) : IsLocalRing N.carrier := N.isLocalRing

/-- Coercion: an N-subring is a subring of T. -/
instance : CoeOut (NSubring T) (Subring T) := ⟨NSubring.carrier⟩

end NSubring

/-!
## A-extension

An A-extension S of an N-subring R is a larger N-subring where prime elements
of R remain prime in S, and |S| ≤ max(ℵ₀, |R|).
-/

/-- S is an A-extension of R if R ≤ S, primes of R remain prime in S,
and the cardinality of S is bounded by max(ℵ₀, |R|). -/
structure IsAExtension (R S : NSubring T) : Prop where
  /-- R is contained in S -/
  le : R.carrier ≤ S.carrier
  /-- Prime elements of R remain prime in S.
  Expressed via the canonical embedding: if r ∈ R is prime, then its image in S is prime. -/
  primes_preserved : ∀ (r : R.carrier), Prime r →
    Prime (⟨r.1, le r.2⟩ : S.carrier)
  /-- |S| ≤ max(ℵ₀, |R|) -/
  card_le : Cardinal.mk S.carrier ≤ max Cardinal.aleph0 (Cardinal.mk R.carrier)

/-!
## Initial N-subring

For T a complete local domain with depth ≥ 2, char 0, and no integer zero divisor,
the prime subring (image of ℤ) localized at M ∩ (prime subring) gives an N-subring.
In characteristic 0 over ℂ, this is essentially ℚ embedded in T.
-/

/-!
## Basic API
-/

/-- The inclusion map from an N-subring into T. -/
def NSubring.subtype (N : NSubring T) : N.carrier →+* T :=
  N.carrier.subtype

/-- Two N-subrings are equal if their carriers are equal. -/
theorem NSubring.ext {N₁ N₂ : NSubring T} (h : N₁.carrier = N₂.carrier) : N₁ = N₂ := by
  cases N₁
  cases N₂
  congr

end
