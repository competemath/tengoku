/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Equivalence proofs for AzMatrix subtraction.
-/
import Tengoku.Azurite.Azurite.AzMatrix.Operations
import Tengoku.Seed.Algebra.Group.Pi.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.Azurite end Tengoku.Azurite open Tengoku.Azurite
namespace Azurite
variable {R : Type _} [Sub R] {m n : Nat}

/-- Subtraction commutes with `toFn`.
@isnad1 id=eq.0h7v.s6.735ccfdd2ef6 from=translated src=- shape=afbc0355 vocab=a52939da
-/
@[simp]
theorem AzMatrix.toFn_sub (M N : AzMatrix R m n) (i : Fin m) (j : Fin n) :
    (M - N).toFn i j = M.toFn i j - N.toFn i j := by
  show (M.zip (· - ·) N).toFn i j = M.toFn i j - N.toFn i j; simp

/-- Subtraction commutes with `ofFn`.
@isnad1 id=eq.0h5v.s6.186483db4e64 from=translated src=- shape=1d6a6513 vocab=febc3c01
-/
@[simp]
theorem AzMatrix.ofFn_sub (f g : Fin m → Fin n → R) :
    AzMatrix.ofFn f - AzMatrix.ofFn g = AzMatrix.ofFn (fun i j => f i j - g i j) := by
  apply AzMatrix.toFn_injective; ext i j; simp

end Azurite
-- Tengoku: root names of this library moved to Tengoku.Azurite so they do not collide with other libraries (generated)
