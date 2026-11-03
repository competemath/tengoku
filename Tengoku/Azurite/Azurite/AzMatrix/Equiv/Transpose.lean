/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Equivalence proofs for AzMatrix transpose.

  Links `AzMatrix.transpose` to Mathlib's `Matrix.transpose`.
-/
import Tengoku.Azurite.Azurite.AzMatrix.Operations
import Tengoku.Seed.Data.Matrix.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Azurite
variable {R : Type _} {m n : Nat}

/-- Transpose commutes with `toFn`.
@isnad1 id=eq.0h4v.s5.1ed4b3908c19 from=translated src=- shape=00bcc00a vocab=3b0e5230
-/
@[simp]
theorem AzMatrix.toFn_transpose (M : AzMatrix R m n) :
    M.transpose.toFn = fun j i => M.toFn i j := by
  ext j i; simp [transpose, toFn, ofFn, get, Vector.get]
  rfl

/-- Transpose commutes with `ofFn`.
@isnad1 id=eq.0h4v.s5.371d54f2c999 from=translated src=- shape=38af89bf vocab=8e8b6de6
-/
@[simp]
theorem AzMatrix.ofFn_transpose (f : Fin m → Fin n → R) :
    (AzMatrix.ofFn f).transpose = AzMatrix.ofFn (fun j i => f i j) := by
  ext j i; simp [transpose, ofFn, get, Vector.get]
  rfl

end Azurite
