/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.Seed.Algebra.MvPolynomial.Division
import Tengoku.Seed.RingTheory.MvPolynomial.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Monomial divisibility and nonzerodivisors without a domain hypothesis

`docs/RECON_PROJECTIVE_TWISTING_BASE_RING.md` locates the entire field dependency of the
`ProjectiveTwisting*` tower in two lemmas of `ProjectiveTwistingSections.lean`, both of which are
*true* over an arbitrary commutative ring but were proved by routes that need a domain:

* `coordinate_pow_dvd_of_dvd_mul_coordinate_pow` is proved from `MvPolynomial.X_prime`, and `X` is
  prime in `R[X]` only when `R` is a domain — yet the statement is a fact about monomial supports;
* the localization comparison uses `powers_le_nonZeroDivisors_of_noZeroDivisors` on `Xᵢ * Xⱼ`, yet a
  monic monomial is a nonzerodivisor over any commutative ring.

This file supplies the domain-free replacements.  Everything it uses from Mathlib
(`monomial_one_dvd_iff_modMonomial_eq_zero`, `coeff_modMonomial_of_le`,
`coeff_modMonomial_of_not_le`, `coeff_mul_monomial`, `coeff_mul_X`) already carries no domain
hypothesis; only `X_prime` and `X_dvd_mul_iff` do, and neither is needed here.

* `MvPolynomial.monomial_one_dvd_iff`: divisibility by a monomial with coefficient `1` is exactly a
  support condition, over any commutative semiring.  This is the general statement behind both
  replacements.
* `MvPolynomial.X_pow_dvd_of_dvd_mul_X_pow`: for `i ≠ j`, if `Xᵢ ^ r` divides `a * Xⱼ ^ m` then it
  divides `a`.  Proved by shifting the exponent vector by `single j m` and reading off the `i`-th
  coordinate, where the shift contributes nothing precisely because `i ≠ j`.
* `MvPolynomial.X_mem_nonZeroDivisors`, `MvPolynomial.X_mul_X_mem_nonZeroDivisors` and
  `MvPolynomial.X_pow_mul_X_pow_mem_nonZeroDivisors`: variables, products of two variables, and
  products of powers of two variables are nonzerodivisors.  The last replaces cancellation by
  `mul_left_cancel₀` (which needs a domain) with cancellation by a nonzerodivisor.
-/

set_option autoImplicit false

universe u v

namespace MvPolynomial

variable {σ : Type u} {R : Type v} [CommSemiring R]

/-- Divisibility by a monomial with coefficient `1` is a support condition: `monomial s 1 ∣ x` iff
every exponent vector occurring in `x` dominates `s`.  No domain hypothesis.-/
theorem monomial_one_dvd_iff {s : σ →₀ ℕ} {x : MvPolynomial σ R} :
    monomial s 1 ∣ x ↔ ∀ t, coeff t x ≠ 0 → s ≤ t := by
  classical
  rw [monomial_one_dvd_iff_modMonomial_eq_zero]
  constructor
  · intro h t ht
    by_contra hle
    apply ht
    rw [← coeff_modMonomial_of_not_le x hle, h, coeff_zero]
  · intro h
    ext t
    rw [coeff_zero]
    by_cases hle : s ≤ t
    · exact coeff_modMonomial_of_le x hle
    · rw [coeff_modMonomial_of_not_le x hle]
      by_contra hc
      exact hle (h t hc)

/-- If `i ≠ j` then `Xᵢ ^ r` divides `a * Xⱼ ^ m` only if it already divides `a`.  Mathlib's route to
this goes through `X_prime`, which needs a domain; this proof is a support computation and holds over
any commutative semiring.-/
theorem X_pow_dvd_of_dvd_mul_X_pow {i j : σ} (hij : i ≠ j) (r m : ℕ) {a : MvPolynomial σ R}
    (h : X i ^ r ∣ a * X j ^ m) : X i ^ r ∣ a := by
  classical
  simp only [X_pow_eq_monomial] at h ⊢
  rw [monomial_one_dvd_iff] at h ⊢
  intro t ht
  have hcoeff : coeff (t + Finsupp.single j m) (a * monomial (Finsupp.single j m) (1 : R)) ≠ 0 := by
    rw [coeff_mul_monomial, mul_one]
    exact ht
  have hle := h _ hcoeff
  rw [Finsupp.single_le_iff] at hle ⊢
  simpa [Finsupp.single_apply, Ne.symm hij] using hle

/-- Every variable is a nonzerodivisor, over any commutative semiring.-/
theorem X_mem_nonZeroDivisors (i : σ) :
    (X i : MvPolynomial σ R) ∈ nonZeroDivisors (MvPolynomial σ R) := by
  have key : ∀ p : MvPolynomial σ R, p * X i = 0 → p = 0 := by
    intro p hp
    ext m
    have hm := congrArg (coeff (m + Finsupp.single i 1)) hp
    rwa [coeff_mul_X, coeff_zero] at hm
  rw [mem_nonZeroDivisors_iff]
  exact ⟨fun x hx => key x (by rwa [mul_comm] at hx), key⟩

/-- A power of a variable is a nonzerodivisor, over any commutative semiring.-/
theorem X_pow_mem_nonZeroDivisors (i : σ) (r : ℕ) :
    (X i ^ r : MvPolynomial σ R) ∈ nonZeroDivisors (MvPolynomial σ R) :=
  pow_mem (X_mem_nonZeroDivisors i) r

/-- The powers of a variable are nonzerodivisors.-/
theorem powers_X_le_nonZeroDivisors (i : σ) :
    Submonoid.powers (X i : MvPolynomial σ R) ≤ nonZeroDivisors (MvPolynomial σ R) :=
  Submonoid.powers_le.mpr (X_mem_nonZeroDivisors i)

/-- A product of two variables is a nonzerodivisor, over any commutative semiring.  This replaces the
appeal to `powers_le_nonZeroDivisors_of_noZeroDivisors` on the overlap equation `Xᵢ * Xⱼ`.-/
theorem X_mul_X_mem_nonZeroDivisors (i j : σ) :
    (X i * X j : MvPolynomial σ R) ∈ nonZeroDivisors (MvPolynomial σ R) :=
  mul_mem (X_mem_nonZeroDivisors i) (X_mem_nonZeroDivisors j)

/-- A product of powers of two variables is a nonzerodivisor.  This replaces cancellation by
`mul_left_cancel₀`, which needs a domain, with cancellation by a nonzerodivisor.-/
theorem X_pow_mul_X_pow_mem_nonZeroDivisors (i j : σ) (r m : ℕ) :
    (X i ^ r * X j ^ m : MvPolynomial σ R) ∈ nonZeroDivisors (MvPolynomial σ R) :=
  mul_mem (pow_mem (X_mem_nonZeroDivisors i) r) (pow_mem (X_mem_nonZeroDivisors j) m)

/-- A finite product of variables is a nonzerodivisor, over any commutative semiring.-/
theorem prod_X_mem_nonZeroDivisors {ι : Type*} (s : Finset ι) (f : ι → σ) :
    (∏ t ∈ s, X (f t) : MvPolynomial σ R) ∈ nonZeroDivisors (MvPolynomial σ R) :=
  prod_mem fun t _ => X_mem_nonZeroDivisors (f t)

/-- The powers of a product of two variables are nonzerodivisors.-/
theorem powers_X_mul_X_le_nonZeroDivisors (i j : σ) :
    Submonoid.powers (X i * X j : MvPolynomial σ R) ≤ nonZeroDivisors (MvPolynomial σ R) :=
  Submonoid.powers_le.mpr (X_mul_X_mem_nonZeroDivisors i j)

end MvPolynomial
