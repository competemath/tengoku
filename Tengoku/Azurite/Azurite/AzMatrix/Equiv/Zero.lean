/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Equivalence proofs for AzMatrix zero.
-/
import Tengoku.Azurite.Azurite.AzMatrix.Operations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Azurite
variable {R : Type _} [Zero R] {m n : Nat}

/-- Zero commutes with `toFn`.
@isnad1 id=eq.0h5v.s5.12c6f3c92544 from=translated src=- shape=34e6e9a8 vocab=310b3957
-/
@[simp]
theorem AzMatrix.toFn_zero (i : Fin m) (j : Fin n) :
    (0 : AzMatrix R m n).toFn i j = 0 := by
  show ((Vector.ofFn (fun _ => Vector.ofFn (fun _ => (0 : R)))).get i).get j = 0
  simp [Vector.get]

/-- Zero commutes with `get`.
@isnad1 id=eq.0h5v.s5.11fdaa323134 from=translated src=- shape=34e6e9a8 vocab=1522de77
-/
@[simp]
theorem AzMatrix.get_zero (i : Fin m) (j : Fin n) :
    (0 : AzMatrix R m n).get i j = 0 := by
  show ((Vector.ofFn (fun _ => Vector.ofFn (fun _ => (0 : R)))).get i).get j = 0
  simp [Vector.get]

/-- Zero commutes with `ofFn`.
@isnad1 id=eq.0h3v.s5.b6366ba10799 from=translated src=- shape=158dc829 vocab=d1daa50c
-/
@[simp]
theorem AzMatrix.ofFn_zero :
    AzMatrix.ofFn (fun (_ : Fin m) (_ : Fin n) => (0 : R)) = (0 : AzMatrix R m n) := rfl

end Azurite
