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

/-- `ofFn` is injective.
@isnad1 id=injectiv.0h2v.s3.cc9d81d755c1 from=translated src=- shape=7de99ee6 vocab=dcd52227
-/
theorem AzVector.ofFn_injective :
    Function.Injective (AzVector.ofFn (R := R) (n := n)) := by
  intro f g h
  funext i
  have := congrArg (fun v => v.toFn i) h
  simp [AzVector.toFn, AzVector.ofFn, Vector.get] at this
  exact this

end Azurite
