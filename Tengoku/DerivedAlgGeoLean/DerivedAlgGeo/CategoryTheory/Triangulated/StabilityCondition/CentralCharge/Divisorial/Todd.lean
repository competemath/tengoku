/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.LinearAlgebra.BilinearForm.Basic
import Tengoku.Seed.Data.Real.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Supplied surface Todd-correction data

On a surface, a Mukai vector uses only the codimension-one component of
`√td` and the integrated codimension-two component.  `SqrtTodd` stores exactly
those two supplied values.  This file makes no claim that they arise from a
scheme; the geometric constructor remains under `AlgebraicGeometry/Numerical`.
-/

universe w

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

variable {D : Type w} [AddCommGroup D] [Module ℝ D]

/-- The part of `√td_X` visible to a surface Mukai vector.-/
structure SqrtTodd (D : Type w) [AddCommGroup D] [Module ℝ D] where
  /-- The codimension-one component `√td₁`.-/
  divisor : D
  /-- The integrated codimension-two component `∫√td₂`.-/
  number : ℝ

namespace SqrtTodd

/-- The trivial correction.-/
def trivial : SqrtTodd D := ⟨0, 0⟩

/-- The K3 correction `√td = 1 + [pt]`.-/
def k3 : SqrtTodd D := ⟨0, 1⟩

/--
@isnad1 id=eq.0h1v.s5.8d931bdd639f from=translated src=- shape=e92d00d1 vocab=b928ca2f
-/
@[simp] theorem trivial_divisor : (trivial : SqrtTodd D).divisor = 0 := rfl

/--
@isnad1 id=eq.0h1v.s4.ce7e312348fd from=translated src=- shape=edd22d68 vocab=6a9141ef
-/
@[simp] theorem trivial_number : (trivial : SqrtTodd D).number = 0 := rfl

/--
@isnad1 id=eq.0h1v.s5.0f2bdc4a02b9 from=translated src=- shape=e92d00d1 vocab=76cc82ee
-/
@[simp] theorem k3_divisor : (k3 : SqrtTodd D).divisor = 0 := rfl

/--
@isnad1 id=eq.0h1v.s4.e599bd25c875 from=translated src=- shape=edd22d68 vocab=3d644705
-/
@[simp] theorem k3_number : (k3 : SqrtTodd D).number = 1 := rfl

end SqrtTodd

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial
