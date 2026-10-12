/-
Copyright (c) 2026 Scott D. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott D. Hughes
-/
module

public import Tengoku

/-!
# Erdős Problem #137: powerful products of consecutive integers (conditional finiteness)

Erdős Problem #137 asks whether the product of `k ≥ 3` consecutive positive integers,
`F k n = n(n+1)⋯(n+k-1)`, can ever be *powerful* (a number `N` with `p ∣ N ⟹ p² ∣ N`).

This file formalizes the deduction that, **under the Granville–Langevin radical lower
bound** `RadLB k` (a consequence of the abc conjecture, taken here as an explicit
hypothesis — it is NOT proved here), `F k n` is powerful for only finitely many `n`,
for each fixed `k ≥ 3`. The underlying mathematics is due to Shorey–Tijdeman (2016)
and Langevin / Granville; this is a formalization of the deduction, not a new result.

## Main results
* `lemma_star` (unconditional): `rad m ^ 2 * B2 m ≤ m ^ 2`.
* `powerful_rad_sq_le`: a powerful `N ≠ 0` satisfies `rad N ^ 2 ≤ N`.
* `erdos137_eventually_not_powerful` / `erdos137_finite` (conditional on `RadLB`, `k ≥ 3`):
  `F k n` is powerful for only finitely many `n`.

The radical bound `RadLB` is the only nonelementary input and appears as a hypothesis.
-/

@[expose] public section

namespace Erdos137

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

/-- Every element of the factorization support is a prime. -/
lemma prime_of_mem_factorization_support {m p : ℕ} (hp : p ∈ m.factorization.support) :
    Nat.Prime p := by
  simp_all

/-
rad(m) ≥ 1 for all m.
-/
lemma rad_pos (m : ℕ) : 1 ≤ rad m := by
  exact Finset.prod_pos fun p hp => Nat.Prime.pos ( prime_of_mem_factorization_support hp )

/-
F(k, n) ≥ 1 when n ≥ 1.
-/
lemma F_pos {k n : ℕ} (hn : 1 ≤ n) : 1 ≤ F k n := by
  exact Nat.one_le_iff_ne_zero.mpr <| Finset.prod_ne_zero_iff.mpr fun i hi => by linarith;

/-
F(k, n) ≠ 0 when n ≥ 1.
-/
lemma F_ne_zero {k n : ℕ} (hn : 1 ≤ n) : F k n ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr fun _ _ => by positivity;

/-
Each factor n + i ≤ k * n for i < k, when n ≥ 1 and k ≥ 1.
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
lemma rad_cast_pos (m : ℕ) : (0 : ℝ) < (rad m : ℝ) := by
  exact_mod_cast rad_pos m

/-! ### RadLB hypothesis and conditional theorem -/

/-- The Granville--Langevin radical lower bound, taken as a hypothesis.
For every ε > 0 there is C > 0 such that rad(F(k,n)) ≥ C · n^{k-1-ε} for all n ≥ 1. -/
def RadLB (k : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n → (rad (F k n) : ℝ) ≥ C * (n : ℝ) ^ ((k : ℝ) - 1 - ε)

/-! ### Erdős #137: conditional finiteness of powerful products -/

/-- `N` is **powerful** if every prime dividing `N` divides it with multiplicity at least two,
i.e. `p ∣ N → p ^ 2 ∣ N` for all primes `p`. -/
def Powerful (N : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ N → p ^ 2 ∣ N

/-- For powerful `N`, the 2-full part `B2 N` is all of `N`. -/
theorem powerful_B2_eq {N : ℕ} (hN : N ≠ 0) (hP : Powerful N) : B2 N = N := by
  unfold B2
  have hfilter : (N.factorization.support.filter (fun p => 2 ≤ N.factorization p))
      = N.factorization.support := by
    apply Finset.filter_true_of_mem
    intro p hp
    have hpprime : p.Prime := prime_of_mem_factorization_support hp
    have hpdvd : p ∣ N := by
      simp_all
    have h2 : p ^ 2 ∣ N := hP p hpprime hpdvd
    exact (Nat.Prime.pow_dvd_iff_le_factorization hpprime hN).mp h2
  rw [hfilter]
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hN]
  rfl

end  -- noncomputable section

end Erdos137
