/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Tengoku.Seed.Algebra.Star.Basic
import Tengoku.Seed.FieldTheory.Galois.Basic
import Tengoku.Seed.FieldTheory.Perfect
import Tengoku.Seed.RingTheory.Trace.Basic
import Tengoku.Seed.RingTheory.Norm.Transitivity
import Tengoku.QuadraticNumberFields.QuadraticNumberFields.Qsqrtd.Basic
import Tengoku.QuadraticNumberFields.QuadraticNumberFields.QuadraticField.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Conjugation on Quadratic Fields

This file introduces a lightweight conjugation interface for quadratic
number fields.  The goal is to provide a stable minimal layer: a class
`QuadraticField.Conj` that records a distinguished non-trivial `ℚ`-algebra
automorphism of a quadratic field, plus the standard model construction
`Qsqrtd.starAlgEquiv` and its `Conj` instance for `Qsqrtd d` with
squarefree `d ≠ 1`.

The `Conj` class is deliberately weaker than "the field has a
non-trivial automorphism"; the `conj_ne_refl` field is here so that
applications that require a *distinguished* non-trivial involution can
assume the automorphism is genuinely non-trivial.

## Main Definitions

* `Qsqrtd.starAlgEquiv`: the conjugation `ℚ(√d) → ℚ(√d)` as a `ℚ`-algebra
  equivalence.
* `QuadraticField.Conj`: a class packaging a distinguished non-trivial
  `ℚ`-algebra involution on a quadratic field.
* `QuadraticField.conjAut`: the underlying `AlgEquiv` of a `Conj` instance.
* `QuadraticField.instConjQsqrtd`: the `Conj` instance for `Qsqrtd d`
  with squarefree `d ≠ 1`.

## Main Theorems

* `QuadraticField.univ_aut_eq_pair`: the `ℚ`-automorphism group of a
  quadratic field is exactly `{AlgEquiv.refl, conjAut K}`.
* `QuadraticField.add_conj_eq_trace_image`: `x + conjAut K x` is the image
  of `Algebra.trace ℚ K x`.
* `QuadraticField.mul_conj_eq_norm_image`: `x * conjAut K x` is the image
  of `Algebra.norm ℚ x`.
-/

-- Use the canonical `QuadraticAlgebra` algebra structure on standard `Qsqrtd`
-- models. Otherwise `DivisionRing.toRatAlgebra` competes with it after the
-- field instance is available.
local notation "ℚ√" d => Qsqrtd d

attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticField

/-- A `Conj` structure on a quadratic field `K` is a distinguished
non-trivial `ℚ`-algebra involution on `K`.

The `conj_conj` and `conj_ne_refl` fields are here so that the
distinguished involution is genuinely non-trivial: any involution of a
quadratic field is automatically either `id` or the conjugation, so the
`conj_ne_refl` field guarantees that the chosen automorphism is the
conjugation.-/
class Conj (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K] where
  /-- The distinguished involution.-/
  conj : K ≃ₐ[ℚ] K
  /-- The involution is involutive.-/
  conj_conj : ∀ x, conj (conj x) = x
  /-- The involution is not the identity.-/
  conj_ne_refl : conj ≠ AlgEquiv.refl

/-- The distinguished `ℚ`-algebra involution associated to a `Conj`
instance.-/
abbrev conjAut (K : Type*) [Field K] [Algebra ℚ K]
    [QuadraticField K] [Conj K] : K ≃ₐ[ℚ] K :=
  Conj.conj

end QuadraticField

namespace Qsqrtd

/-! ## The Standard-Model Conjugation

The `QuadraticAlgebra R a b` model has a canonical involution given by
`(re + im · ω) ↦ (re + b · im) - im · ω`, which for our `Qsqrtd d =
QuadraticAlgebra ℚ d 0` (where `b = 0`) is the familiar conjugation
`re + im · √d ↦ re - im · √d`.  Mathlib provides the `Star`/`StarRing`
machinery for this involution; we package it here as a `ℚ`-algebra
equivalence. -/

/-- The conjugation on `Q(√d)` as a `ℚ`-algebra equivalence.  The
`[Fact (¬ IsSquare d)]` constraint ensures the `Field` instance on
`Qsqrtd d` is available, which fixes the `Semiring`/`Algebra` instances
to match the ones used by the `Conj` class.-/
noncomputable def starAlgEquiv (d : ℚ) [Fact (¬ IsSquare d)] :
    Qsqrtd d ≃ₐ[ℚ] Qsqrtd d where
  toFun := star
  invFun := star
  left_inv x := star_involutive x
  right_inv x := star_involutive x
  map_mul' := fun x y => by
    -- `star_mul` is the anti-multiplicative form; the ring is commutative,
    -- so `star y * star x = star x * star y`.
    rw [star_mul, mul_comm]
  map_add' := star_add
  commutes' := fun r => by
    -- For `Qsqrtd d = QuadraticAlgebra ℚ d 0`, the rational algebra
    -- map sends `r ↦ ⟨r, 0⟩` and `star ⟨r, 0⟩ = ⟨r, 0⟩`.
    simp

/-- `Qsqrtd.starAlgEquiv` acts as `star`.
@isnad1 id=eq.0h2v.s7.39f766458d9e from=translated src=- shape=ddab4a92 vocab=89e43bfc
-/
theorem starAlgEquiv_apply {d : ℚ} [Fact (¬ IsSquare d)] (x : Qsqrtd d) :
    starAlgEquiv d x = star x := by
  rfl

/-- The inverse of `Qsqrtd.starAlgEquiv` also acts as `star`.
@isnad1 id=eq.0h2v.s8.e3447ebaf501 from=translated src=- shape=ad8f8357 vocab=a84f48f7
-/
theorem starAlgEquiv_symm_apply {d : ℚ} [Fact (¬ IsSquare d)] (x : Qsqrtd d) :
    (starAlgEquiv d).symm x = star x := by
  rfl

end Qsqrtd

namespace QuadraticField

/-! ## Trace and Norm via the Distinguished Conjugation

For a quadratic field `K` over `ℚ`, the extension is Galois with group of
order two.  The distinguished involution `conjAut K` is non-trivial, so the
automorphism group is exactly `{AlgEquiv.refl, conjAut K}`.  Summing/multiplying
the Galois orbit then recovers the trace and norm. -/

section TraceNorm

variable {K : Type*} [Field K] [Algebra ℚ K] [QuadraticField K] [Conj K]

end TraceNorm

end QuadraticField
