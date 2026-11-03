/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Equivalence proof for AzVector scalar multiplication.
-/
import Tengoku.Azurite.Azurite.AzVector.Operations
import Tengoku.Seed.Algebra.Group.Pi.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Azurite
variable {R : Type _} {n : Nat}

/-- Scalar multiplication commutes with `toFn`.
@isnad1 id=eq.0h5v.s6.5fbb9e7b8e05 from=translated src=- shape=9b03f1ec vocab=cf4d4d7c
-/
@[simp]
theorem AzVector.toFn_smul' [SMul α R] (c : α) (v : AzVector R n) :
    (c • v).toFn = c • v.toFn := AzVector.toFn_smul c v

/-- Scalar multiplication commutes with `ofFn`.
@isnad1 id=eq.0h5v.s6.8c089b01e088 from=translated src=- shape=90c958ce vocab=ee843ebc
-/
@[simp]
theorem AzVector.ofFn_smul [SMul α R] (c : α) (f : Fin n → R) :
    AzVector.ofFn (c • f) = c • (AzVector.ofFn f) := by
  apply AzVector.toFn_injective; ext i; simp

end Azurite
