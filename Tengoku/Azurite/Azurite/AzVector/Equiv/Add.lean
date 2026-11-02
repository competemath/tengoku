/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Equivalence proof for AzVector addition.
-/
import Tengoku.Azurite.Azurite.AzVector.Operations
import Tengoku.Seed.Algebra.Group.Pi.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Azurite
variable {R : Type _} [Add R] {n : Nat}

/-- Addition commutes with `toFn`.-/
@[simp]
theorem AzVector.toFn_add' (v w : AzVector R n) :
    (v + w).toFn = v.toFn + w.toFn := AzVector.toFn_add v w

/-- Addition commutes with `ofFn`.-/
@[simp]
theorem AzVector.ofFn_add (f g : Fin n → R) :
    AzVector.ofFn (f + g) = AzVector.ofFn f + AzVector.ofFn g := by
  apply AzVector.toFn_injective; ext i; simp

end Azurite
