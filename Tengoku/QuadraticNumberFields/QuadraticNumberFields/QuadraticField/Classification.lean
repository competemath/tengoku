/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Tengoku.QuadraticNumberFields.QuadraticNumberFields.QuadraticField.Parameters
import Tengoku.QuadraticNumberFields.QuadraticNumberFields.QuadraticField.Basic
import Tengoku.Seed.FieldTheory.PrimitiveElement
import Tengoku.Seed.Algebra.Polynomial.Degree.IsMonicOfDegree
import Tengoku.Seed.Algebra.Field.Equiv
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Classification of Quadratic Fields by Squarefree Integer Parameters

This file proves that a field over `ℚ` is quadratic exactly when it is
isomorphic to one of the explicit models `Qsqrtd (z : ℚ) = ℚ(√z)` with
`z : ℤ` squarefree and `z ≠ 1`.

## Main Theorems

* `exists_squarefree_int_param_of_isQuadraticField`: every quadratic field is
  isomorphic to `Qsqrtd (z : ℚ)` for some squarefree integer `z ≠ 1`.
* `exists_algEquiv_qsqrtd`: the same classification interface stated using the
  `[QuadraticField K]` abstraction.
* `exists_ringEquiv_qsqrtd`: the ring-equivalence shadow of the classification
  interface, useful for invariants that do not depend on the chosen `ℚ`-algebra
  structure.
* `isQuadraticField_iff_exists_squarefree_int_param`: characterization of
  quadratic fields via the normalized models `Qsqrtd (z : ℚ)`.

## Implementation note

The standard model declarations use the canonical `QuadraticAlgebra` algebra
structure on `Qsqrtd`, avoiding the `ℚ`-algebra diamond with
`DivisionRing.toRatAlgebra`.
-/

local notation "ℚ√" d => Qsqrtd d

attribute [-instance] DivisionRing.toRatAlgebra

open scoped QuadraticAlgebra
open Polynomial IntermediateField

/-- `d` is a normalized standard parameter for the abstract quadratic field `K`
if it is squarefree, not equal to `1`, and `K` is isomorphic to `Qsqrtd d`.-/
def IsStandardParameter (K : Type*) [Field K] [Algebra ℚ K] (d : ℤ) : Prop :=
  Squarefree d ∧ d ≠ 1 ∧ Nonempty (K ≃ₐ[ℚ] Qsqrtd (d : ℚ))
