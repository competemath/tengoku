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

> **Entry**: functional-analysis.baire.theorem
@isnad1 id=dense.2h2v.s6.63ead4c18126 from=translated src=- shape=3ee2cc32 vocab=463643bf
-/
theorem banach_dense_iInter_of_isOpen {U : ℕ → Set E}
    (hOpen : ∀ n, IsOpen (U n)) (hDense : ∀ n, Dense (U n)) :
    Dense (⋂ n, U n) := by
  exact dense_iInter_of_isOpen_nat hOpen hDense

/-- Closed-cover form of Baire: if countably many closed sets cover a nonempty Banach space, one
of them has nonempty interior.
@isnad1 id=ex.2h2v.s6.8166711d535d from=translated src=- shape=51b4942a vocab=8d31e600
-/
theorem banach_nonempty_interior_of_iUnion_of_closed [Nonempty E] {F : ℕ → Set E}
    (hClosed : ∀ n, IsClosed (F n)) (hCover : ⋃ n, F n = Set.univ) :
    ∃ n, (interior (F n)).Nonempty := by
  exact nonempty_interior_of_iUnion_of_closed hClosed hCover

end SandronesLibrary.FunctionalAnalysis
