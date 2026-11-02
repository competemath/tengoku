/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Equivalence proofs for AzVector: ofFn injectivity.
-/
import Tengoku.Azurite.Azurite.AzVector.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Azurite
variable {R : Type _} {n : Nat}

/-- `ofFn` is injective.-/
theorem AzVector.ofFn_injective :
    Function.Injective (AzVector.ofFn (R := R) (n := n)) := by
  intro f g h
  funext i
  have := congrArg (fun v => v.toFn i) h
  simp [AzVector.toFn, AzVector.ofFn, Vector.get] at this
  exact this

end Azurite
