/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Tengoku.Seed.Data.Int.Basic
import Tengoku.Seed.Data.Int.GCD
import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Binary Quadratic Forms

This file defines the project-owned integer-triple model of binary quadratic
forms used for the Cox/Gauss class-group bridge.

## Implementation notes

Mathlib has structural `QuadraticForm`s, but this subsystem uses the classical
coordinate model for integral binary forms. The direct `(a, b, c)`
representation gives computable coefficient access, the classical discriminant
normalization `b² - 4ac`, and derived `DecidableEq` / `Repr` instances used by
reduced-form enumeration and compile-time regression checks.
-/

namespace QuadraticNumberFields

/-- An integral binary quadratic form `a X² + b X Y + c Y²`.-/
structure BinaryQuadraticForm where
  /-- The `X²` coefficient.-/
  a : ℤ
  /-- The `XY` coefficient.-/
  b : ℤ
  /-- The `Y²` coefficient.-/
  c : ℤ
deriving DecidableEq, Repr

-- The `prec` argument of the derived `Repr` instance is unused for a plain
-- product structure; this is inherent to the `Repr.reprPrec` signature.
attribute [nolint unusedArguments] instReprBinaryQuadraticForm.repr

namespace BinaryQuadraticForm

/--
@isnad1 id=eq.3h2v.s4.95b2bd6e1cc9 from=translated src=- shape=966c8f3f vocab=2e9f6fb2
-/
@[ext] theorem ext {Q R : BinaryQuadraticForm}
    (ha : Q.a = R.a) (hb : Q.b = R.b) (hc : Q.c = R.c) : Q = R := by
  cases Q
  cases R
  simp_all

/-- The discriminant `b² - 4ac` of a binary quadratic form.-/
def disc (Q : BinaryQuadraticForm) : ℤ :=
  Q.b ^ 2 - 4 * Q.a * Q.c

/-- Evaluation of `a X² + b X Y + c Y²` at integer coordinates.-/
def eval (Q : BinaryQuadraticForm) (x y : ℤ) : ℤ :=
  Q.a * x ^ 2 + Q.b * x * y + Q.c * y ^ 2

/-- A form has a prescribed discriminant.-/
def HasDiscriminant (Q : BinaryQuadraticForm) (D : ℤ) : Prop :=
  Q.disc = D

/-- Positive definiteness in the imaginary quadratic setting.-/
def IsPositiveDefinite (Q : BinaryQuadraticForm) : Prop :=
  0 < Q.a ∧ Q.disc < 0

/-- Primitive forms have coprime coefficients.-/
def IsPrimitive (Q : BinaryQuadraticForm) : Prop :=
  Int.gcd Q.a (Int.gcd Q.b Q.c) = 1

/--
@isnad1 id=eq.0h3v.s5.7296c5a97762 from=translated src=- shape=aa48115a vocab=fdda163c
-/
@[simp] theorem disc_mk (a b c : ℤ) :
    disc (BinaryQuadraticForm.mk a b c) = b ^ 2 - 4 * a * c := rfl

/--
@isnad1 id=eq.0h5v.s6.0982a9fa691b from=translated src=- shape=b2f27708 vocab=5b69ad9d
-/
@[simp] theorem eval_mk (a b c x y : ℤ) :
    eval (BinaryQuadraticForm.mk a b c) x y =
      a * x ^ 2 + b * x * y + c * y ^ 2 := rfl

end BinaryQuadraticForm
end QuadraticNumberFields
