/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
import Tengoku.Tauceti.TauCeti.NumberTheory.NumberField.PrimeIdeal

/-!
# An effective count of ideals of bounded norm

In a number field `F` of degree `n`, the number of nonzero integral ideals of norm at most
`X` is at most `X² · 2ⁿ`. A nonzero ideal is encoded injectively as an `n`-tuple of positive
naturals with product `≤ absNorm I` (distributing, for each rational prime `p`, the value
`p^{vₚ}` of the `i`-th prime above `p` into the `i`-th coordinate); the valuations of the
tuple recover the ideal, and there are at most `X²·2ⁿ` such tuples.

Mathlib's `Ideal.finite_setOfPred_absNorm_le` already gives finiteness (and `Ideal/Asymptotics`
the sharp asymptotic `~ ρ·X`); the contribution here is the explicit elementary bound, the
input to the effective class-number estimate.

## Main result

* `NumberField.card_ideal_absNorm_le`: at most `X²·2^[F:ℚ]` nonzero ideals of norm
  `≤ X`.

The `Consumer` section at the end restates this bound in the natural-number and degree-monotone
forms later effective estimates use (`ncard_ideal_absNorm_le_nat`,
`ncard_ideal_absNorm_le_of_nat_le_of_finrank_le`, `ncard_ideal_absNorm_le_of_finrank_le`,
`ncard_ideal_absNorm_le_nat_of_finrank_le`).

## Provenance

Migrated from
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the
formalization of L. Alpöge's disproof of the uniform-constant Erdős unit-distance
conjecture, where this Rankin-style count fed the class-number bound.
-/

public section

attribute [local instance] Classical.propDecidable

namespace NumberField

/-- The set of `n`-tuples of positive naturals with real product at most `X`. -/
private def prodLeTuples (n : ℕ) (X : ℝ) : Set (Fin n → ℕ) :=
  {d : Fin n → ℕ | (∀ i, 0 < d i) ∧ (∏ i, (d i : ℝ)) ≤ X}

@[simp]
private theorem mem_prodLeTuples {n : ℕ} {X : ℝ} {d : Fin n → ℕ} :
    d ∈ prodLeTuples n X ↔ (∀ i, 0 < d i) ∧ (∏ i, (d i : ℝ)) ≤ X := Iff.rfl

/-! ### Encoding ideals as tuples (for the Rankin-style ideal count)

We encode a nonzero ideal `I` of `𝓞 F` as an `n`-tuple of positive naturals
(`n = [F:ℚ]`) whose product is at most `absNorm I`, injectively. For a nonzero
prime `P`, `absNormUnder P` is the norm of the rational prime below `P` and `primeCoord P`
is the index of `P` among the (at most `n`) primes above that rational prime. The
`i`-th coordinate of the encoding multiplies `(absNormUnder P) ^ (mult of P in I)`
over all prime factors `P` of `I` with `primeCoord P = i`. -/
section RankinCount

open _root_.NumberField Ideal IsDedekindDomain UniqueFactorizationMonoid

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

/-- The norm of the rational prime below a prime ideal `P` of `𝓞 F`. -/
private def absNormUnder (P : Ideal (𝓞 F)) : ℕ := Ideal.absNorm (Ideal.under ℤ P)

/-- The coordinate (index in `Fin [F:ℚ]`) assigned to a prime ideal `P`: its
position in the list of primes above the rational prime below `P`. -/
private def primeCoord (P : Ideal (𝓞 F)) : ℕ :=
  (IsDedekindDomain.primesOverFinset (Ideal.under ℤ P) (𝓞 F)).toList.idxOf P

/-- The `i`-th coordinate of the tuple encoding the ideal `I`. -/
private def encodeIdeal (I : Ideal (𝓞 F)) (i : Fin (Module.finrank ℚ F)) : ℕ :=
  ∏ P ∈ (normalizedFactors I).toFinset.filter (fun P => primeCoord F P = i.val),
    (absNormUnder F P) ^ ((normalizedFactors I).count P)

/-
[foundational] `P` belongs to the finite set of primes above the rational
prime below it.
-/

/-
[foundational] The coordinate of a nonzero prime ideal is `< [F:ℚ]`.
-/

/-
[foundational] `absNormUnder` injectivity: equal `absNormUnder` means the primes lie
over the same rational prime, hence have the same `IsDedekindDomain.primesOverFinset`.
-/

/-
[foundational] A nonzero prime and an ideal over the same rational prime with the
same coordinate are equal.  Only `P` need be assumed prime and nonzero: the shared
coordinate places `Q` at `P`'s index in the list of primes over that rational prime,
which already forces `Q` to lie in it.
-/

/-
[foundational] Each coordinate of the encoding of a nonzero ideal is positive.
-/

/-
Regrouping: the product of all coordinates is the product over all prime
factors of `(absNormUnder P) ^ (mult of P)`.
-/

/-
The product of the encoding coordinates is at most `absNorm I`.
-/

/-
Recovery: the multiplicity of a prime `P` in `I` is the `absNormUnder P`-adic
valuation of the `primeCoord P` coordinate of the encoding.
-/

/-
[foundational] The encoding is injective on nonzero ideals.
-/

end

end RankinCount

/-! ## Consumer forms

These are direct corollaries of `card_ideal_absNorm_le`, packaging its real norm bound as the
natural-number and degree-monotone forms that later effective estimates carry. -/

section Consumer

open scoped _root_.NumberField

open Module _root_.NumberField

/-- The set of nonzero integral ideals of `𝓞 F` with natural norm at most `N`. -/
private abbrev idealsWithAbsNormNatLe (F : Type*) [Field F] [NumberField F] (N : ℕ) :
    Set (Ideal (𝓞 F)) :=
  {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ Ideal.absNorm I ≤ N}

/-- The set of nonzero integral ideals of `𝓞 F` with real norm at most `X`. -/
private abbrev idealsWithAbsNormRealLe (F : Type*) [Field F] [NumberField F] (X : ℝ) :
    Set (Ideal (𝓞 F)) :=
  {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}

end Consumer

end NumberField
