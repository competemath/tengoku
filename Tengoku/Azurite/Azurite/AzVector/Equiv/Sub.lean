/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Equivalence proof for AzVector subtraction.
-/
import Tengoku.Azurite.Azurite.AzVector.Operations
import Tengoku.Seed.Algebra.Group.Pi.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.Azurite end Tengoku.Azurite open Tengoku.Azurite
namespace Azurite
variable {R : Type _} [Sub R] {n : Nat}

/-- Subtraction commutes with `toFn`.
@isnad1 id=eq.0h4v.s6.b3bfa43328cf from=translated src=- shape=74e2239c vocab=5693f962
-/
@[simp]
theorem AzVector.toFn_sub' (v w : AzVector R n) :
    (v - w).toFn = v.toFn - w.toFn := AzVector.toFn_sub v w

/-- Subtraction commutes with `ofFn`.
@isnad1 id=eq.0h4v.s6.d9d24d6819eb from=translated src=- shape=a0978e6a vocab=d0cc0880
-/
@[simp]
theorem AzVector.ofFn_sub (f g : Fin n → R) :
    AzVector.ofFn (f - g) = AzVector.ofFn f - AzVector.ofFn g := by
  apply AzVector.toFn_injective; ext i; simp

end Azurite
-- Tengoku: root names of this library moved to Tengoku.Azurite so they do not collide with other libraries (generated)
