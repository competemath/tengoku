/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Tengoku.QuadraticNumberFields.QNFMathlib.Algebra.QuadraticAlgebra.Basic
import Tengoku.QuadraticNumberFields.QuadraticNumberFields.Zsqrtd.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Pell-Type Equations

This file connects integer solutions of the Pell-type equations `x² - d·y² = n`
with norm-`n` elements of the project model `ℤ[√d]`, and builds explicit units
of `ℤ[√d]` from norm-`±1` solutions.

## Main definitions

* `IsPellSolution d n x y`: the pair `(x, y)` solves `x² - d·y² = n`.
* `IsPellUnitSolution d x y`: solutions of the norm-one Pell equation.
* `IsPellUnitSolution.unit`: the explicit unit of `ℤ[√d]` attached to a
  norm-one Pell solution.
* `IsPellSolution.negOneUnit`: the explicit unit attached to a norm-`-1`
  solution.

## Main results

* `isPellSolution_iff_norm_eq`: Pell solutions are exactly the coordinates of
  norm-`n` elements of `ℤ[√d]`.
* `IsPellSolution.mul`: Brahmagupta composition of Pell solutions.
* `isUnit_mk_iff_isPellSolution`: `x + y√d` is a unit of `ℤ[√d]` iff `(x, y)`
  solves `x² - d·y² = 1` or `x² - d·y² = -1`.
-/

local notation "ℚ√" d => Qsqrtd d

namespace QuadraticNumberFields
namespace Units

open QuadraticAlgebra

/-- Integer solutions to `x ^ 2 - d * y ^ 2 = n`.-/
def IsPellSolution (d n x y : ℤ) : Prop :=
  x ^ 2 - d * y ^ 2 = n

/-- Integer solutions to the norm-one Pell equation.-/
def IsPellUnitSolution (d x y : ℤ) : Prop :=
  IsPellSolution d 1 x y

/-- Pell solutions for `n` are exactly the coordinates of norm-`n` elements of
`ℤ[√d]`.
@isnad1 id=iff.0h4v.s4.0c96cfc79c55 from=translated src=- shape=041dfc66 vocab=4926cb92
-/
theorem isPellSolution_iff_norm_eq {d n x y : ℤ} :
    IsPellSolution d n x y ↔ Zsqrtd.norm (⟨x, y⟩ : Zsqrtd d) = n := by
  unfold IsPellSolution
  rw [Zsqrtd.norm_mk]

/-- The trivial solution of the norm-one Pell equation.
@isnad1 id=ispellun.0h1v.s3.fcc86802e4e5 from=translated src=- shape=4fca81ff vocab=a5e3e542
-/
theorem isPellUnitSolution_one_zero (d : ℤ) : IsPellUnitSolution d 1 0 := by
  unfold IsPellUnitSolution IsPellSolution
  ring

/-- Negating `x` preserves Pell solutions.
@isnad1 id=ispellso.1h4v.s4.0a86c9b8bc8f from=translated src=- shape=24bfdbb3 vocab=e939a5a0
-/
theorem IsPellSolution.neg_left {d n x y : ℤ} (h : IsPellSolution d n x y) :
    IsPellSolution d n (-x) y := by
  unfold IsPellSolution at h ⊢
  rw [← h]; ring

/-- Negating `y` preserves Pell solutions.
@isnad1 id=ispellso.1h4v.s4.3a1b3f630833 from=translated src=- shape=48ad96be vocab=e939a5a0
-/
theorem IsPellSolution.neg_right {d n x y : ℤ} (h : IsPellSolution d n x y) :
    IsPellSolution d n x (-y) := by
  unfold IsPellSolution at h ⊢
  rw [← h]; ring

/-- Brahmagupta composition: a solution for `m` and a solution for `n` compose
to a solution for `m * n`, with the coordinates of the product
`(x₁ + y₁√d)(x₂ + y₂√d)` in `ℤ[√d]`.
@isnad1 id=ispellso.2h7v.s6.e78de0f2da83 from=translated src=- shape=7d54cad8 vocab=2990e162
-/
theorem IsPellSolution.mul {d m n x₁ y₁ x₂ y₂ : ℤ} (h₁ : IsPellSolution d m x₁ y₁)
    (h₂ : IsPellSolution d n x₂ y₂) :
    IsPellSolution d (m * n) (x₁ * x₂ + d * y₁ * y₂) (x₁ * y₂ + y₁ * x₂) := by
  unfold IsPellSolution at h₁ h₂ ⊢
  rw [← h₁, ← h₂]; ring

/-- Norm-one Pell solutions are closed under Brahmagupta composition.
@isnad1 id=ispellun.2h5v.s6.c18bbe4d4c13 from=translated src=- shape=7a21f973 vocab=850ff6ce
-/
theorem IsPellUnitSolution.mul {d x₁ y₁ x₂ y₂ : ℤ} (h₁ : IsPellUnitSolution d x₁ y₁)
    (h₂ : IsPellUnitSolution d x₂ y₂) :
    IsPellUnitSolution d (x₁ * x₂ + d * y₁ * y₂) (x₁ * y₂ + y₁ * x₂) := by
  simpa [IsPellUnitSolution] using IsPellSolution.mul h₁ h₂

/-- The explicit unit of `ℤ[√d]` attached to a norm-one Pell solution; the
inverse is the conjugate `x - y√d`.-/
def IsPellUnitSolution.unit {d x y : ℤ} (h : IsPellUnitSolution d x y) : (Zsqrtd d)ˣ :=
  unitOfNormOne ⟨x, y⟩ (isPellSolution_iff_norm_eq.mp h)

/--
@isnad1 id=eq.1h3v.s5.4c649ab833ab from=translated src=- shape=a866ad28 vocab=f63691b6
-/
@[simp]
theorem IsPellUnitSolution.val_unit {d x y : ℤ} (h : IsPellUnitSolution d x y) :
    (h.unit : Zsqrtd d) = ⟨x, y⟩ :=
  rfl

/-- The explicit unit of `ℤ[√d]` attached to a norm-`-1` Pell solution; the
inverse is the negated conjugate `-(x - y√d)`.-/
def IsPellSolution.negOneUnit {d x y : ℤ} (h : IsPellSolution d (-1) x y) : (Zsqrtd d)ˣ :=
  unitOfNormNegOne ⟨x, y⟩ (isPellSolution_iff_norm_eq.mp h)

/--
@isnad1 id=eq.1h3v.s5.6d622a5bc809 from=translated src=- shape=ccbe1c43 vocab=bb416619
-/
@[simp]
theorem IsPellSolution.val_negOneUnit {d x y : ℤ} (h : IsPellSolution d (-1) x y) :
    (h.negOneUnit : Zsqrtd d) = ⟨x, y⟩ :=
  rfl

/-- `x + y√d` is a unit of `ℤ[√d]` iff `(x, y)` solves `x² - d·y² = ±1`.
@isnad1 id=iff.0h3v.s6.379cdb111c34 from=translated src=- shape=808ab5b8 vocab=77f05216
-/
theorem isUnit_mk_iff_isPellSolution {d x y : ℤ} :
    IsUnit (⟨x, y⟩ : Zsqrtd d) ↔ IsPellSolution d 1 x y ∨ IsPellSolution d (-1) x y := by
  rw [isUnit_iff_norm_isUnit, Int.isUnit_iff, isPellSolution_iff_norm_eq,
      isPellSolution_iff_norm_eq]

/-- A norm-one Pell solution with `y ≠ 0` produces a unit different from `1`.
@isnad1 id=ne.2h3v.s6.9964b2796d4c from=translated src=- shape=2d96c6f6 vocab=9b16d416
-/
theorem IsPellUnitSolution.unit_ne_one {d x y : ℤ} (h : IsPellUnitSolution d x y)
    (hy : y ≠ 0) : h.unit ≠ 1 := by
  intro heq
  apply hy
  simpa [im_one] using congrArg (fun u : (Zsqrtd d)ˣ => (u : Zsqrtd d).im) heq

/-- A norm-one Pell solution with `y ≠ 0` produces a unit different from `-1`.
@isnad1 id=ne.2h3v.s7.d671d6554c23 from=translated src=- shape=d5ffa897 vocab=45a0254c
-/
theorem IsPellUnitSolution.unit_ne_neg_one {d x y : ℤ} (h : IsPellUnitSolution d x y)
    (hy : y ≠ 0) : h.unit ≠ -1 := by
  intro heq
  apply hy
  simpa [im_one] using congrArg (fun u : (Zsqrtd d)ˣ => (u : Zsqrtd d).im) heq

/-- A norm-negative-one Pell solution with `y ≠ 0` produces a unit different from `1`.
@isnad1 id=ne.2h3v.s6.dcbb1818b29b from=translated src=- shape=7576d925 vocab=b22c48ce
-/
theorem IsPellSolution.negOneUnit_ne_one {d x y : ℤ} (h : IsPellSolution d (-1) x y)
    (hy : y ≠ 0) : h.negOneUnit ≠ 1 := by
  intro heq
  apply hy
  simpa [im_one] using congrArg (fun u : (Zsqrtd d)ˣ => (u : Zsqrtd d).im) heq

/-- A norm-negative-one Pell solution with `y ≠ 0` produces a unit different from `-1`.
@isnad1 id=ne.2h3v.s7.d95aee70457c from=translated src=- shape=4406e09e vocab=b22c48ce
-/
theorem IsPellSolution.negOneUnit_ne_neg_one {d x y : ℤ} (h : IsPellSolution d (-1) x y)
    (hy : y ≠ 0) : h.negOneUnit ≠ -1 := by
  intro heq
  apply hy
  simpa [im_one] using congrArg (fun u : (Zsqrtd d)ˣ => (u : Zsqrtd d).im) heq

end Units
end QuadraticNumberFields
