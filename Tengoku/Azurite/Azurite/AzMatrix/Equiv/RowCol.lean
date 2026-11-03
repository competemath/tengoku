/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Equivalence proofs for AzMatrix row and column access.
-/
import Tengoku.Azurite.Azurite.AzMatrix.RowCol
import Tengoku.Azurite.Azurite.AzVector.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Azurite
variable {R : Type _} {m n : Nat}

/-- Row extraction commutes with `toFn`: the `i`-th row of `M`
    is `M.toFn i` as a function `Fin n → R`.
@isnad1 id=eq.0h5v.s5.b9ca1041c706 from=translated src=- shape=f517af18 vocab=fd40e722
-/
theorem AzMatrix.toFn_row (M : AzMatrix R m n) (i : Fin m) :
    (M.row i).toFn = M.toFn i := by
  ext j; simp [row, AzVector.toFn, AzMatrix.toFn, Vector.get]

/-- Column extraction commutes with `toFn`: the `j`-th column of `M`
    is `fun i => M.toFn i j` as a function `Fin m → R`.
@isnad1 id=eq.0h5v.s5.7ec0ac216149 from=translated src=- shape=fd8cdd44 vocab=193fba3d
-/
theorem AzMatrix.toFn_col (M : AzMatrix R m n) (j : Fin n) :
    (M.col j).toFn = fun i => M.toFn i j := by
  ext i; simp [col, AzVector.toFn, AzMatrix.toFn, get, Vector.get]
  rfl

/-- `ofRows` commutes with `toFn`.
@isnad1 id=eq.0h6v.s5.bc1aa5d7ff32 from=translated src=- shape=3a4a32da vocab=53888092
-/
theorem AzMatrix.toFn_ofRows (rows : Vector (AzVector R n) m) (i : Fin m) (j : Fin n) :
    (AzMatrix.ofRows rows).toFn i j = (rows.get i).data.get j := by
  simp [ofRows, AzMatrix.toFn, Vector.get, Vector.map]
  rfl

/-- `ofCols` commutes with `toFn`.
@isnad1 id=eq.0h6v.s5.68830e98e92b from=translated src=- shape=27a900ec vocab=0f4bc21d
-/
theorem AzMatrix.toFn_ofCols (cols : Vector (AzVector R m) n) (i : Fin m) (j : Fin n) :
    (AzMatrix.ofCols cols).toFn i j = (cols.get j).data.get i := by
  simp [ofCols, AzMatrix.toFn, AzMatrix.ofFn, Vector.get]
  rfl

end Azurite
