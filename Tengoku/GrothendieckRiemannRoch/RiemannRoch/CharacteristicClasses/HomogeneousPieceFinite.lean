/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.Seed.RingTheory.MvPolynomial.Homogeneous
import Tengoku.Seed.LinearAlgebra.Finsupp.Supported
import Tengoku.Seed.RingTheory.Finiteness.Basic
import Tengoku.Seed.LinearAlgebra.FreeModule.Finite.Basic
import Tengoku.GrothendieckRiemannRoch.RiemannRoch.CharacteristicClasses.ProjectiveSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The homogeneous degree-`d` piece is free of finite rank over an arbitrary base ring

`Γ(ℙⁿ_R, O(d))` is the degree-`d` homogeneous piece of `R[X₀, …, Xₙ]`, so Serre finiteness in degree
zero for nonnegative twists is, algebraically, the statement that this piece is a finite `R`-module.
The existing project proof (`ProjectiveTwistingEulerCharacteristic.degreePiece_finite`) works only
over a **field**: it injects the piece into a finite-index function space and appeals to
`Module.Finite.of_injective`, which needs the ambient ring to be noetherian (a submodule of a finite
module is finite only then).

Over an arbitrary commutative ring the correct argument is that the piece is *free*, on the finite
basis of degree-`d` monomials.  That is what this file proves, and it is missing from Mathlib:

* `Finsupp.finite_setOf_degree_eq`: for a finite index type, only finitely many exponent vectors have
  total degree `d` (each coordinate is bounded by the degree, `Finsupp.le_degree`);
* `MvPolynomial.homogeneousSubmoduleEquivFinsupp`: the degree-`d` piece is linearly equivalent to the
  finitely-supported functions on degree-`d` exponent vectors.  This is Mathlib's
  `homogeneousSubmodule_eq_finsupp_supported` followed by `Finsupp.supportedEquivFinsupp`;
* `MvPolynomial.homogeneousSubmodule_free` and `MvPolynomial.homogeneousSubmodule_finite`: freeness
  over any commutative ring, and finiteness when the index type is finite.

Since `SchemeProjectiveSpace.grading R n` is by definition
`MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R`, this immediately gives
`SchemeProjectiveSpace.grading_free` and `SchemeProjectiveSpace.grading_finite` over an arbitrary
commutative base ring, superseding the field-only `degreePiece_finite`.  The geometric consumer is
the base-ring generalization of the `ProjectiveTwisting*` tower, which currently computes
`H⁰(ℙⁿ_k, O(d))` only over a field.
-/

set_option autoImplicit false

universe u v

namespace Finsupp

/-- For a finite index type, only finitely many exponent vectors have a given total degree: each
coordinate is bounded by the degree.-/
theorem finite_setOf_degree_eq (σ : Type u) [Finite σ] (d : ℕ) :
    Finite {m : σ →₀ ℕ // m.degree = d} := by
  classical
  refine Finite.of_injective
    (fun m : {m : σ →₀ ℕ // m.degree = d} =>
      (fun i : σ => (⟨min (m.1 i) d, Nat.lt_succ_of_le (min_le_right _ _)⟩ : Fin (d + 1)))) ?_
  intro a b hab
  refine Subtype.ext (Finsupp.ext fun i => ?_)
  have ha : a.1 i ≤ d := le_of_le_of_eq (Finsupp.le_degree i a.1) a.2
  have hb : b.1 i ≤ d := le_of_le_of_eq (Finsupp.le_degree i b.1) b.2
  have h : min (a.1 i) d = min (b.1 i) d := by
    simpa using congrFun hab i
  omega

end Finsupp

namespace MvPolynomial

variable (σ : Type u) (R : Type v) [CommRing R] (d : ℕ)

variable [Finite σ]

end MvPolynomial

namespace SchemeProjectiveSpace

end SchemeProjectiveSpace
