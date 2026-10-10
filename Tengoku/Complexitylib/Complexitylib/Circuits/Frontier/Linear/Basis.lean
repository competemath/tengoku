/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Tengoku.Complexitylib.Complexitylib.Cslib.Circuit.Upstream
public import Tengoku

/-!
# Affine, polynomial, and arithmetic bases

Three ways of computing over a field `F`:

* the *affine basis* (`Frontier.affineSignature`), whose operations of arity `k` are the affine
  maps `x ↦ a₀ x₀ + ... + a_{k-1} x_{k-1} + b`;
* *polynomial interpretations* (`Frontier.IsPolynomial`), in which every operation of a
  signature is a polynomial in its arguments, with any coefficients and of any degree;
* the *arithmetic basis* (`Frontier.arithSignature`): addition, multiplication, and a constant
  gate for each element of `F`.

Arithmetic circuits are polynomial. Over a finite field every operation is polynomial, so the
distinction matters only over infinite fields, where it is essential: an infinite field admits
bijections `F × F → F`, through which a single wire can carry any amount of information.

In arithmetic circuits the constants are leaves, and `Cslib.Circuits.Circuit.innerSize` counts
exactly the additions and multiplications.
-/

@[expose] public section

namespace Complexity.Frontier

open Cslib.Circuits

universe u

variable (F : Type u)

/-- The operations of the arithmetic basis. -/
inductive ArithOp : Type u
  /-- Addition. -/
  | add
  /-- Multiplication. -/
  | mul
  /-- A constant. -/
  | const (c : F)

/-- The arity of an arithmetic operation. -/
abbrev ArithOp.arity : ArithOp F → ℕ
  | .add => 2
  | .mul => 2
  | .const _ => 0

variable {F}

end Complexity.Frontier
