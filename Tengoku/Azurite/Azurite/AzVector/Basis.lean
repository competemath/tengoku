/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Standard basis vectors for AzVector.
-/
import Tengoku.Azurite.Azurite.AzVector.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Azurite
variable {R : Type _} {n : Nat}

/-- The `i`-th standard basis vector: 1 at index `i`, 0 elsewhere.-/
def AzVector.stdBasis [Zero R] [One R] (i : Fin n) : AzVector R n :=
  ⟨Vector.ofFn (fun j => if i = j then 1 else 0)⟩

/--
@isnad1 id=eq.0h3v.s4.df691c21ebff from=translated src=- shape=5c7a7d7c vocab=5917a477
-/
@[simp]
theorem AzVector.get_stdBasis_self [Zero R] [One R] (i : Fin n) :
    (AzVector.stdBasis i).get i = (1 : R) := by
  simp [AzVector.get, stdBasis, Vector.get]
  intro hne
  exact absurd rfl hne

/--
@isnad1 id=eq.1h4v.s5.ab96224c1d34 from=translated src=- shape=efe10b89 vocab=5917a477
-/
theorem AzVector.get_stdBasis_ne [Zero R] [One R] {i j : Fin n} (h : i ≠ j) :
    (AzVector.stdBasis i).get j = (0 : R) := by
  simp [AzVector.get, stdBasis, Vector.get]
  intro hij
  exact absurd hij h

end Azurite
