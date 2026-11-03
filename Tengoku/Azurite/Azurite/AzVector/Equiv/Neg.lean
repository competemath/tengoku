/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Equivalence proof for AzVector negation.
-/
import Tengoku.Azurite.Azurite.AzVector.Operations
import Tengoku.Seed.Algebra.Group.Pi.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Azurite
variable {R : Type _} [Neg R] {n : Nat}

/-- Negation commutes with `toFn`.
@isnad1 id=eq.0h3v.s5.35392f15a91c from=translated src=- shape=7fee339f vocab=7ed8808a
-/
@[simp]
theorem AzVector.toFn_neg' (v : AzVector R n) :
    (-v).toFn = -v.toFn := AzVector.toFn_neg v

/-- Negation commutes with `ofFn`.
@isnad1 id=eq.0h3v.s5.238595cd7368 from=translated src=- shape=5a6333d6 vocab=7ffe64e4
-/
@[simp]
theorem AzVector.ofFn_neg (f : Fin n → R) :
    AzVector.ofFn (-f) = -(AzVector.ofFn f) := by
  apply AzVector.toFn_injective; ext i; simp

end Azurite
