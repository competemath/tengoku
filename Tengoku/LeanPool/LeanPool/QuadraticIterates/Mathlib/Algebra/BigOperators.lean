/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Tengoku

/-!
# Big-operator lemmas

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

/-- Factor a constant out of an indicator-weighted sum: `∑ g x · [p x]·c = c · ∑_{p x} g x`.
@isnad1 id=eq.0h6v.s6.d4c068f46ba7 from=translated src=- shape=2ac4f4cd vocab=7a104f20
-/
theorem Finset.sum_mul_ite_const {ι R : Type*} [CommSemiring R] (s : Finset ι) (p : ι → Prop)
    [DecidablePred p] (g : ι → R) (c : R) :
    ∑ x ∈ s, g x * (if p x then c else 0) = c * ∑ x ∈ s with p x, g x := by
  simp_rw [mul_ite, mul_zero, ← Finset.sum_filter]
  rw [← Finset.sum_mul, mul_comm]

/-- An `𝔽₂`-linear combination is the sum over the support of the coefficient function.
@isnad1 id=eq.0h4v.s8.96bfa7e617e7 from=translated src=- shape=fb6a3c8c vocab=db772c7b
-/
theorem sum_zmod_two_smul_eq_sum_filter {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    [Module (ZMod 2) M] (m : ι → M) (g : ι → ZMod 2) :
    ∑ i, g i • m i = ∑ i ∈ Finset.univ with g i = 1, m i := by
  have h01 : ∀ z : ZMod 2, z ≠ 1 → z = 0 := by decide
  rw [← Finset.sum_subset (Finset.filter_subset (fun i ↦ g i = 1) Finset.univ)
    (fun i _ hi ↦ by rw [h01 (g i) (by simpa using hi), zero_smul])]
  exact Finset.sum_congr rfl fun i hi ↦ by rw [(Finset.mem_filter.mp hi).2, one_smul]
