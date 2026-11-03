/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Equivalence proofs for AzMatrix: ofFn injectivity.
-/
import Tengoku.Azurite.Azurite.AzMatrix.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Azurite
variable {R : Type _} {m n : Nat}

/-- `ofFn` is injective.
@isnad1 id=injectiv.0h3v.s4.e3e66d3a8a2d from=translated src=- shape=754975c7 vocab=b818dc1d
-/
theorem AzMatrix.ofFn_injective :
    Function.Injective (AzMatrix.ofFn (R := R) (m := m) (n := n)) := by
  intro f g h
  funext i j
  have := congrArg (fun M => M.toFn i j) h
  simp [AzMatrix.toFn, AzMatrix.ofFn, Vector.get] at this
  exact this

end Azurite
