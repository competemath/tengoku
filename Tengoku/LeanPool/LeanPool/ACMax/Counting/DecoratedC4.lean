/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Tengoku
public import Tengoku.LeanPool.LeanPool.ACMax.Counting.SparseCore

/-!
# Decorated four-cycle cuts at order fifteen

Two compact sparse-cut certificates used by the endpoint shared-star census.
The four-cycle itself misses the order-15 cut inequality by one edge; adjoining
one parent, or two adjacent parents, supplies exactly the missing slack.
-/

@[expose] public section

namespace ACMax

open Finset

noncomputable section

/-- Use the same finite-set decisions as the classical graph certificates. -/
local instance decoratedCycleFinDecidableEq {n : ℕ} : DecidableEq (Fin n) := Classical.decEq _

end

end ACMax
