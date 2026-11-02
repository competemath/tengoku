/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Equivalence proofs for AzVector standard basis.

  Proves `toFn (stdBasis i) j = if i = j then 1 else 0`
  and links `stdBasis` to `Pi.single` via `ofFn`.
-/
import Tengoku.Azurite.Azurite.AzVector.Basis
import Tengoku.Azurite.Azurite.AzVector.Operations
import Tengoku.Seed.Algebra.Group.Pi.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Azurite
variable {R : Type _} [Zero R] [One R] {n : Nat}

/-- Standard basis commutes with `toFn`: yields the indicator function.-/
theorem AzVector.toFn_stdBasis (i j : Fin n) :
    (AzVector.stdBasis (R := R) i).toFn j = if i = j then 1 else 0 := by
  simp [AzVector.toFn, stdBasis, Vector.get, Vector.ofFn]
  rfl

/-- `Pi.single` maps back to `stdBasis` via `ofFn`.-/
theorem AzVector.ofFn_indicator (i : Fin n) :
    AzVector.ofFn (fun j => if i = j then (1 : R) else 0) = AzVector.stdBasis i := by
  ext j; simp [AzVector.ofFn, stdBasis, Vector.ofFn]

end Azurite
