/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.Seed.Algebra.Ring.GeomSum
import Tengoku.Seed.Algebra.BigOperators.Ring.Finset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Algebraic core of Adams–Riemann–Roch for closed immersions

Pure commutative algebra, no schemes.

* `SchemeKTheory.ARR.adams_prod_one_sub`: if `ψ` is a ring endomorphism with `ψ ℓᵢ = ℓᵢ ^ j`,
  then `ψ (∏ (1 - ℓᵢ)) = ∏ (∑_{a<j} ℓᵢ^a) · ∏ (1 - ℓᵢ)`. This is the split form of
  `ψʲ(λ₋₁ V) = θʲ(V) · λ₋₁(V)`, from `1 - ℓʲ = (1 + ℓ + ⋯ + ℓ^{j-1})(1 - ℓ)`.
* `SchemeKTheory.ARR.adams_push_of_koszul`: the zero-section (Koszul) case of `ψʲ(i_* x) =
  i_*(θʲ(N^∨) · ψʲ x)` as a formal consequence of the projection formula, a retraction
  `s^* ∘ p^* = id`, `i_* 1 = λ₋₁(Q^∨)`, the identity for `λ₋₁(Q^∨)` and `s^* θ(Q^∨) = θ(N^∨)`.
-/

set_option autoImplicit false

namespace SchemeKTheory.ARR

variable {A : Type*} [CommRing A]

/-- `1 - ℓʲ = (∑_{a<j} ℓ^a) (1 - ℓ)`.
@isnad1 id=eq.0h3v.s7.316ba1175b7c from=translated src=- shape=d46d0bb6 vocab=cd0d0923
-/
theorem one_sub_pow_eq_geom_mul (ℓ : A) (j : ℕ) :
    1 - ℓ ^ j = (∑ a ∈ Finset.range j, ℓ ^ a) * (1 - ℓ) := by
  rw [mul_comm, mul_neg_geom_sum]

/-- **Split form of `ψʲ(λ₋₁V) = θʲ(V)·λ₋₁(V)`.**
@isnad1 id=eq.1h6v.s8.7fc05f6c49dc from=translated src=- shape=97804bd4 vocab=d89eec40
-/
theorem adams_prod_one_sub {ι : Type*} (s : Finset ι) (ψ : A →+* A) (j : ℕ) (ℓ : ι → A)
    (hψ : ∀ i ∈ s, ψ (ℓ i) = ℓ i ^ j) :
    ψ (∏ i ∈ s, (1 - ℓ i)) =
      (∏ i ∈ s, ∑ a ∈ Finset.range j, ℓ i ^ a) * ∏ i ∈ s, (1 - ℓ i) := by
  rw [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [map_sub, map_one, hψ i hi, one_sub_pow_eq_geom_mul]

/-- **Adams–RR for a section with a Koszul class (formal part).**

`p : A_Z → A_P` is the pullback along the bundle projection, `s : A_P → A_Z` the pullback along
the zero section (`s ∘ p = id`), `push` the pushforward along the section, satisfying the
projection formula. If `push 1 = λ` (Koszul), `ψ_P λ = t_P · λ` and `s t_P = t_Z`, then
`ψ_P (push x) = push (ψ_Z x · t_Z)`.
@isnad1 id=eq.6h11v.s9.85c550d5c3c2 from=translated src=- shape=424f3754 vocab=7b780836
-/
theorem adams_push_of_koszul {AZ AP : Type*} [CommRing AZ] [CommRing AP]
    (ψZ : AZ →+* AZ) (ψP : AP →+* AP) (p : AZ →+* AP) (s : AP →+* AZ)
    (hsp : ∀ x, s (p x) = x) (hψp : ∀ x, ψP (p x) = p (ψZ x))
    (push : AZ →+ AP) (proj : ∀ y x, push (s y * x) = y * push x)
    (lam tP : AP) (tZ : AZ) (koszul : push 1 = lam) (hlam : ψP lam = tP * lam)
    (ht : s tP = tZ) (x : AZ) :
    ψP (push x) = push (ψZ x * tZ) := by
  have hpush : ∀ z, push z = p z * lam := fun z => by
    rw [← koszul, ← proj, mul_one, hsp]
  have hz : ψZ x * tZ = s (p (ψZ x) * tP) * 1 := by
    rw [mul_one, map_mul, hsp, ht]
  rw [hpush, map_mul, hlam, hψp, hz, proj, koszul, mul_assoc]

end SchemeKTheory.ARR
