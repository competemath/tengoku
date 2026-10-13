/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Claude
-/
module

public import Tengoku
public import Tengoku.Flt.FLT.Mathlib.FieldTheory.Galois.Basic

/-!
# Trace and norm in a separable quadratic extension

Proposed new Mathlib file `Mathlib.RingTheory.Norm.Quadratic`: trace and norm via the
nontrivial automorphism of a separable quadratic extension.
-/

@[expose] public section

open Algebra.IsQuadraticExtension

section

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]

/-- In a separable quadratic extension, the trace of `x` is `x + σx`, where `σ` is the
nontrivial automorphism.
@isnad1 id=eq.1h4v.s9.1816ad3df858 from=translated src=- shape=4375ff07 vocab=5d9435a2
-/
theorem Algebra.IsQuadraticExtension.algebraMap_trace_eq_add {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1)
    (x : L) : algebraMap K L (Algebra.trace K L x) = x + σ x := by
  classical
  rw [trace_eq_sum_automorphisms, univ_algEquiv K L hσ, Finset.sum_pair (Ne.symm hσ)]
  simp

/-- In a separable quadratic extension, the norm of `x` is `x * σx`, where `σ` is the
nontrivial automorphism.
@isnad1 id=eq.1h4v.s8.03fc0f3740e7 from=translated src=- shape=160499dc vocab=fb482cc1
-/
theorem Algebra.IsQuadraticExtension.algebraMap_norm_eq_mul {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1)
    (x : L) : algebraMap K L (Algebra.norm K x) = x * σ x := by
  classical
  rw [Algebra.norm_eq_prod_automorphisms, univ_algEquiv K L hσ, Finset.prod_pair (Ne.symm hσ)]
  simp

/-- The trace of `b + aθ` in a separable quadratic extension is `a·tr(θ) + 2b`.
@isnad1 id=eq.0h5v.s9.b5f21d85d528 from=translated src=- shape=00d5691b vocab=ae72ec43
-/
theorem Algebra.IsQuadraticExtension.trace_algebraMap_add_algebraMap_mul (a b : K) (θ : L) :
    Algebra.trace K L (algebraMap K L b + algebraMap K L a * θ)
      = a * Algebra.trace K L θ + 2 * b := by
  obtain ⟨σ, hσ⟩ := exists_algEquiv_ne_one K L
  apply FaithfulSMul.algebraMap_injective K L
  simp only [map_add, map_mul, map_ofNat, algebraMap_trace_eq_add K L hσ, AlgEquiv.commutes]
  ring

/-- The norm of `b + aθ` in a separable quadratic extension is `b² + ab·tr(θ) + a²·N(θ)`.
@isnad1 id=eq.0h5v.s9.076651efb4a2 from=translated src=- shape=ee61d929 vocab=9e38b743
-/
theorem Algebra.IsQuadraticExtension.norm_algebraMap_add_algebraMap_mul (a b : K) (θ : L) :
    Algebra.norm K (algebraMap K L b + algebraMap K L a * θ)
      = b ^ 2 + a * b * Algebra.trace K L θ + a ^ 2 * Algebra.norm K θ := by
  obtain ⟨σ, hσ⟩ := exists_algEquiv_ne_one K L
  apply FaithfulSMul.algebraMap_injective K L
  simp only [map_add, map_mul, map_pow, algebraMap_trace_eq_add K L hσ,
    algebraMap_norm_eq_mul K L hσ, AlgEquiv.commutes]
  ring

/-- If `θ` generates a separable quadratic extension of `K` — that is, lies outside `K` — and
`t`, `n` denote its trace and norm, so that `θ² = tθ - n`, then the discriminant `t² - 4n` of
the minimal polynomial of `θ` is nonzero. (Over the nontrivial automorphism `σ` it equals
`(θ - σθ)²` with `σθ ≠ θ`. In characteristic 2 the statement says `t ≠ 0`: separable quadratic
extensions are Artin–Schreier extensions.)
@isnad1 id=ne.1h3v.s8.0850736be47b from=translated src=- shape=5eecc018 vocab=bed18fc1
-/
theorem Algebra.IsQuadraticExtension.discrim_ne_zero {θ : L}
    (hθ : θ ∉ Set.range (algebraMap K L)) :
    Algebra.trace K L θ ^ 2 - 4 * Algebra.norm K θ ≠ 0 := by
  obtain ⟨σ, hσ⟩ := exists_algEquiv_ne_one K L
  intro h0
  have h1 : (θ - σ θ) ^ 2 = 0 := by
    have h2 := congrArg (algebraMap K L) h0
    simp only [map_sub, map_pow, map_mul, map_zero, map_ofNat,
      algebraMap_trace_eq_add K L hσ, algebraMap_norm_eq_mul K L hσ] at h2
    linear_combination h2
  exact algEquiv_apply_ne K L hσ hθ
    (sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h1)).symm

/-- A square root `α ∉ K` of an element of `K` has trace `0`: the nontrivial automorphism
sends `α` to `-α` (`Algebra.IsQuadraticExtension.algEquiv_apply_eq_neg_of_sq_eq`).
@isnad1 id=eq.2h4v.s8.ece92f10ddcf from=translated src=- shape=9889c07f vocab=4c781db0
-/
theorem Algebra.IsQuadraticExtension.trace_eq_zero_of_sq_eq {α : L} {d : K}
    (hαK : α ∉ Set.range (algebraMap K L)) (hα : α ^ 2 = algebraMap K L d) :
    Algebra.trace K L α = 0 := by
  obtain ⟨σ, hσ⟩ := exists_algEquiv_ne_one K L
  apply FaithfulSMul.algebraMap_injective K L
  rw [algebraMap_trace_eq_add K L hσ, algEquiv_apply_eq_neg_of_sq_eq K L hσ hαK hα, map_zero,
    add_neg_cancel]

/-- A square root `α ∉ K` of `d ∈ K` has norm `-d`: the nontrivial automorphism sends `α`
to `-α` (`Algebra.IsQuadraticExtension.algEquiv_apply_eq_neg_of_sq_eq`).
@isnad1 id=eq.2h4v.s8.e462bfdfc599 from=translated src=- shape=e284b12e vocab=42f0b84d
-/
theorem Algebra.IsQuadraticExtension.norm_eq_neg_of_sq_eq {α : L} {d : K}
    (hαK : α ∉ Set.range (algebraMap K L)) (hα : α ^ 2 = algebraMap K L d) :
    Algebra.norm K α = -d := by
  obtain ⟨σ, hσ⟩ := exists_algEquiv_ne_one K L
  apply FaithfulSMul.algebraMap_injective K L
  rw [algebraMap_norm_eq_mul K L hσ, algEquiv_apply_eq_neg_of_sq_eq K L hσ hαK hα, map_neg, ← hα]
  ring

end

end
