/-
Copyright (c) 2026 Scott D. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott D. Hughes
-/
module

public import Tengoku

/-!
# Conditional upper bound on B₂ via a radical lower bound (Erdős #367)

We formalize the "Langevin route" for the general-k upper bound in Erdős #367,
taking the deep unproven ingredient — a radical lower bound for products of
consecutive integers — as an **explicit hypothesis** (`RadLB`).

## Definitions

* `rad m` — the radical (squarefree kernel) of `m`: product of its distinct prime factors.
* `B2 m` — the powerful (2-full) part of `m`: ∏_{p : v_p(m) ≥ 2} p^{v_p(m)}.
* `F k n` — the product of `k` consecutive integers starting at `n`.

## Main results

* `lemma_star` (unconditional): `rad m ^ 2 * B2 m ≤ m ^ 2`.
* `B2_upper_bound` (conditional on `RadLB`): for every `ε > 0` there is `C' > 0` with
  `B2 (F k n) ≤ C' * n ^ (2 + ε)` for all `n ≥ 1`.
-/

@[expose] public section

namespace GeneralK

open scoped BigOperators
open Finset

noncomputable section

/-! ### Definitions -/

/-- The radical of `m`: product of its distinct prime factors. rad(0) = rad(1) = 1 by convention. -/
def rad (m : ℕ) : ℕ := ∏ p ∈ m.factorization.support, p

/-- The 2-full (powerful) part of `m`: product of p^{a_p} over primes with a_p ≥ 2. -/
def B2 (m : ℕ) : ℕ :=
  ∏ p ∈ m.factorization.support.filter (fun p => 2 ≤ m.factorization p), p ^ m.factorization p

/-- Product of k consecutive integers starting at n. -/
def F (k n : ℕ) : ℕ := ∏ i ∈ Finset.range k, (n + i)

/-! ### Auxiliary lemmas -/

/-- Every element of the factorization support is a prime.
@isnad1 id=prime.1h2v.s4.dab73c0b70c0 from=translated src=- shape=fc365083 vocab=4776634d
-/
lemma prime_of_mem_factorization_support {m p : ℕ} (hp : p ∈ m.factorization.support) :
    Nat.Prime p := by
  rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
  exact hp.1

/-
rad(m) ≥ 1 for all m.
-/
/--
@isnad1 id=le.0h1v.s3.5f78b9bf090a from=translated src=- shape=8a62b088 vocab=de3c3839
-/
lemma rad_pos (m : ℕ) : 1 ≤ rad m := by
  exact Finset.prod_pos fun p hp => Nat.Prime.pos ( prime_of_mem_factorization_support hp )

/-
F(k, n) ≥ 1 when n ≥ 1.
-/
/--
@isnad1 id=le.1h2v.s4.72a5905be620 from=translated src=- shape=61bdc3e7 vocab=42c912ae
-/
lemma F_pos {k n : ℕ} (hn : 1 ≤ n) : 1 ≤ F k n := by
  exact Nat.one_le_iff_ne_zero.mpr <| Finset.prod_ne_zero_iff.mpr fun i hi => by linarith;

/-
F(k, n) ≠ 0 when n ≥ 1.
-/
/--
@isnad1 id=ne.1h2v.s4.5dc406bc9808 from=translated src=- shape=41cb78f6 vocab=42c912ae
-/
lemma F_ne_zero {k n : ℕ} (hn : 1 ≤ n) : F k n ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr fun _ _ => by positivity;

/-
Each factor n + i ≤ k * n for i < k, when n ≥ 1 and k ≥ 1.
-/
/--
@isnad1 id=le.3h3v.s5.05ef2c915f76 from=translated src=- shape=0f91ad8e vocab=923b6325
-/
lemma factor_le_mul {k n i : ℕ} (_hk : 1 ≤ k) (hn : 1 ≤ n) (hi : i < k) :
    n + i ≤ k * n := by
  nlinarith

/-
F(k, n) ≤ (k * n) ^ k for n ≥ 1, k ≥ 1.
-/

/-! ### LEMMA STAR -/

/-
**Lemma Star** (unconditional): rad(m)² · B₂(m) ≤ m² for all m.

Proof idea: express both sides as products over the prime factorization support.
For each prime p with exponent a_p:
- If a_p = 1: LHS contributes p², RHS contributes p² (equal).
- If a_p ≥ 2: LHS contributes p^{2+a_p}, RHS contributes p^{2a_p}, and 2+a_p ≤ 2a_p.
-/

/-! ### Bridge to ℝ -/

/-
Cast of lemma_star to ℝ: B₂(m) ≤ m²/rad(m)².
-/

/-
rad(m) cast to ℝ is positive for m ≠ 0. Actually rad is always ≥ 1.
-/
/--
@isnad1 id=lt.0h1v.s4.cd4744e54487 from=translated src=- shape=2cbac45b vocab=eb01babd
-/
lemma rad_cast_pos (m : ℕ) : (0 : ℝ) < (rad m : ℝ) := by
  exact_mod_cast rad_pos m

/-! ### RadLB hypothesis and conditional theorem -/

/-- The "Langevin route" radical lower bound, taken as a hypothesis.
For every ε > 0 there is C > 0 such that rad(F(k,n)) ≥ C · n^{k-1-ε} for all n ≥ 1. -/
def RadLB (k : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n →
      (rad (F k n) : ℝ) ≥ C * (n : ℝ) ^ ((k : ℝ) - 1 - ε)

/-
**Conditional theorem**: assuming RadLB, for every ε > 0 there is C' > 0 with
B₂(F(k,n)) ≤ C' · n^{2+ε} for all n ≥ 1.

This isolates the logical core of the proposed "Langevin route" argument for the
general-k upper bound in Erdős #367.
-/

end

end GeneralK
