/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Equivalence proofs for AzMatrix negation.
-/
import Tengoku.Azurite.Azurite.AzMatrix.Operations
import Tengoku.Seed.Algebra.Group.Pi.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.Azurite end Tengoku.Azurite open Tengoku.Azurite
namespace Azurite
variable {R : Type _} [Neg R] {m n : Nat}

/-- Negation commutes with `toFn`.
@isnad1 id=eq.0h6v.s5.ae589bfd51be from=translated src=- shape=c5a79bc9 vocab=9b5025be
-/
@[simp]
theorem AzMatrix.toFn_neg (M : AzMatrix R m n) (i : Fin m) (j : Fin n) :
    (-M).toFn i j = -(M.toFn i j) := by
  show (M.map (- ·)).toFn i j = -(M.toFn i j); simp

/-- Negation commutes with `ofFn`.
@isnad1 id=eq.0h4v.s5.bc3e2e6443d4 from=translated src=- shape=8a6efc68 vocab=17a0921a
-/
@[simp]
theorem AzMatrix.ofFn_neg (f : Fin m → Fin n → R) :
    -(AzMatrix.ofFn f) = AzMatrix.ofFn (fun i j => -(f i j)) := by
  apply AzMatrix.toFn_injective; ext i j; simp

end Azurite
-- Tengoku: root names of this library moved to Tengoku.Azurite so they do not collide with other libraries (generated)
