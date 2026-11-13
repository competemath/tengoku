/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Equivalence proofs for AzMatrix addition.
-/
import Tengoku.Azurite.Azurite.AzMatrix.Operations
import Tengoku.Seed.Algebra.Group.Pi.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.Azurite end Tengoku.Azurite open Tengoku.Azurite
namespace Azurite
variable {R : Type _} [Add R] {m n : Nat}

/-- Addition commutes with `toFn`.
@isnad1 id=eq.0h7v.s6.87c3ecf8a3b5 from=translated src=- shape=afbc0355 vocab=0cf0f4ae
-/
@[simp]
theorem AzMatrix.toFn_add (M N : AzMatrix R m n) (i : Fin m) (j : Fin n) :
    (M + N).toFn i j = M.toFn i j + N.toFn i j := by
  show (M.zip (· + ·) N).toFn i j = M.toFn i j + N.toFn i j; simp

/-- Addition commutes with `ofFn`.
@isnad1 id=eq.0h5v.s6.a140a8a4842f from=translated src=- shape=1d6a6513 vocab=5007b095
-/
@[simp]
theorem AzMatrix.ofFn_add (f g : Fin m → Fin n → R) :
    AzMatrix.ofFn f + AzMatrix.ofFn g = AzMatrix.ofFn (fun i j => f i j + g i j) := by
  apply AzMatrix.toFn_injective; ext i j; simp

end Azurite
-- Tengoku: root names of this library moved to Tengoku.Azurite so they do not collide with other libraries (generated)
