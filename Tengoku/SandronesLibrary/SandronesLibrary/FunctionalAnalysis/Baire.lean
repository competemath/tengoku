/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.NormedSpace
import Tengoku.Seed.Topology.Baire.CompleteMetrizable
import Tengoku.Seed.Topology.Baire.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Baire theorem for Banach spaces

Mathlib's `BaireSpace` states exactly that a countable intersection of dense open sets is dense.
Every Banach space carries this property through its complete metric.  This file exposes the
textbook statement and its closed-cover form without introducing a parallel Baire predicate.
-/

namespace SandronesLibrary.FunctionalAnalysis

open Set
open SandronesLibrary.Topology.NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedLinearSpace ℝ E] [BanachSpace E]

/-- **Baire category theorem for Banach spaces**: a countable intersection of dense open sets is
dense.

The family is indexed by `ℕ`, matching the textbook meaning of “countably many”.

> **Entry**: functional-analysis.baire.theorem-/
theorem banach_dense_iInter_of_isOpen {U : ℕ → Set E}
    (hOpen : ∀ n, IsOpen (U n)) (hDense : ∀ n, Dense (U n)) :
    Dense (⋂ n, U n) := by
  exact dense_iInter_of_isOpen_nat hOpen hDense

/-- Closed-cover form of Baire: if countably many closed sets cover a nonempty Banach space, one
of them has nonempty interior.-/
theorem banach_nonempty_interior_of_iUnion_of_closed [Nonempty E] {F : ℕ → Set E}
    (hClosed : ∀ n, IsClosed (F n)) (hCover : ⋃ n, F n = Set.univ) :
    ∃ n, (interior (F n)).Nonempty := by
  exact nonempty_interior_of_iUnion_of_closed hClosed hCover

end SandronesLibrary.FunctionalAnalysis
