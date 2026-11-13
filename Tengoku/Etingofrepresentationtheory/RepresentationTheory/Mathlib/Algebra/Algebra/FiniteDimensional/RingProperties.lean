/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Tengoku.Seed.RingTheory.Artinian.Module
import Tengoku.Seed.RingTheory.Jacobson.Semiprimary
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Defs
import Tengoku.Seed.Algebra.Algebra.Tower

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace RepresentationTheory.Mathlib.Algebra.Algebra.FiniteDimensional.RingProperties

/-- A ring that is finite-dimensional as an algebra over a field is Artinian.-/
theorem FiniteDimensional.isArtinianRing
    (k A : Type*) [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] :
    IsArtinianRing A :=
  isArtinian_of_tower k inferInstance

/-- A ring that is finite-dimensional as an algebra over a field is semiprimary.-/
theorem FiniteDimensional.isSemiprimaryRing
    (k A : Type*) [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] :
    IsSemiprimaryRing A :=
  haveI : IsArtinianRing A := FiniteDimensional.isArtinianRing k A
  inferInstance

end RepresentationTheory.Mathlib.Algebra.Algebra.FiniteDimensional.RingProperties
