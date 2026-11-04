/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Equivalence proof for AzVector zero.
-/
import Tengoku.Azurite.Azurite.AzVector.Operations
import Tengoku.Seed.Algebra.Group.Pi.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Azurite
variable {R : Type _} [Zero R] {n : Nat}

/-- Zero commutes with `toFn`.
@isnad1 id=eq.0h2v.s5.7283f1d5f920 from=translated src=- shape=bcb28051 vocab=6fda637b
-/
@[simp]
theorem AzVector.toFn_zero' :
    (0 : AzVector R n).toFn = 0 := AzVector.toFn_zero

/-- Zero commutes with `ofFn`.
@isnad1 id=eq.0h2v.s5.3fadd5c583d8 from=translated src=- shape=1d964f14 vocab=9d6ed096
-/
@[simp]
theorem AzVector.ofFn_zero :
    AzVector.ofFn (0 : Fin n → R) = (0 : AzVector R n) := by
  apply AzVector.toFn_injective; ext i; simp

end Azurite
