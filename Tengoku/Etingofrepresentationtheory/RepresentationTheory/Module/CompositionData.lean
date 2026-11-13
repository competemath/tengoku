/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Tengoku.Seed.Order.RelSeries
import Tengoku.Seed.Algebra.Module.Submodule.Lattice

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Module composition data -/

namespace RepresentationTheory.Module.CompositionData

/-- Inductive data associated with a module from which an increasing relational series of submodules is obtained.-/
structure ModuleCompositionData (A : Type*) (V : Type*)
    [Ring A] [AddCommGroup V] [Module A V] where
  /-- The relational series of submodules determined by module composition data.-/
  toRelSeries : RelSeries {p : Submodule A V × Submodule A V | p.1 < p.2}
  /-- The first submodule in the relational series determined by module composition data is the bottom submodule.-/
  toRelSeries_head : toRelSeries.head = ⊥
  /-- The last submodule in the relational series determined by module composition data is the top submodule.-/
  toRelSeries_last : toRelSeries.last = ⊤

end RepresentationTheory.Module.CompositionData
