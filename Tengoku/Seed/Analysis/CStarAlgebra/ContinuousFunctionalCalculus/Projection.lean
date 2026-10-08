/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Tengoku.Seed.FieldTheory.IsAlgClosed.Spectrum

/-! # Continuous functional calculus and projections

This file collects some results related to projections, idempotents,
and the continuous functional calculus. -/

public section

section Field
variable (R : Type*) {A : Type*} {p : A → Prop} [Field R] [StarRing R] [MetricSpace R]
  [IsTopologicalSemiring R] [ContinuousStar R] [TopologicalSpace A]

/--
@isnad1 id=iff.0h5v.s8.56f5f8a6b24c from=seed src=0 shape=dd8c4d24 vocab=d67efc0a
-/
theorem isIdempotentElem_iff_quasispectrum_subset [NonUnitalRing A] [StarRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] [NonUnitalContinuousFunctionalCalculus R A p]
    (a : A) (ha : p a) : IsIdempotentElem a ↔ quasispectrum R a ⊆ {0, 1} := by
  refine ⟨IsIdempotentElem.quasispectrum_subset R, fun h ↦ ?_⟩
  rw [IsIdempotentElem, ← cfcₙ_id' R a, ← cfcₙ_mul _ _]
  exact cfcₙ_congr fun x hx ↦ by grind

/--
@isnad1 id=iff.0h5v.s7.6bc1ccce49c4 from=seed src=0 shape=fc631059 vocab=aa40446b
-/
theorem isIdempotentElem_iff_spectrum_subset [Ring A] [StarRing A] [Algebra R A]
    [NonUnitalContinuousFunctionalCalculus R A p] (a : A) (ha : p a) :
    IsIdempotentElem a ↔ spectrum R a ⊆ {0, 1} := by
  grind [quasispectrum_eq_spectrum_union_zero, isIdempotentElem_iff_quasispectrum_subset R]

end Field

/--
@isnad1 id=iff.0h2v.s8.5e4156c093cb from=seed src=0 shape=2a7f7996 vocab=c3b344d0
-/
theorem isIdempotentElem_star_mul_self_iff_isIdempotentElem_self_mul_star {A : Type*}
    [TopologicalSpace A] [NonUnitalRing A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A]
    [SMulCommClass ℝ A A] [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    {x : A} : IsIdempotentElem (star x * x) ↔ IsIdempotentElem (x * star x) := by
  simp [isIdempotentElem_iff_quasispectrum_subset ℝ, quasispectrum.mul_comm]
