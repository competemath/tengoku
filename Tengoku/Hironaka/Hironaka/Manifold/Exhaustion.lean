/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Tengoku.Seed.Geometry.Manifold.ChartedSpace
public import Tengoku.Seed.Analysis.RCLike.Basic
public import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Defs
import Tengoku.Seed.Analysis.RCLike.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Relatively compact exhaustion of a manifold

A Hausdorff, second countable manifold modelled on a locally compact space is locally compact and
σ-compact, and Mathlib's `CompactExhaustion` gives compact sets `K_0 ⊆ int K_1 ⊆ K_1 ⊆ …` with
`⋃ K_n = M`. This module defines the relatively compact open subsets `M_n := int K_{n+1}`
(`relCompactOpen`) and records their properties: each `M_n` is open with compact closure,
`closure M_n ⊆ M_{n+1}`, the `M_n` increase, and `⋃ M_n = M`.

These are the open subsets over which the analytic resolution is built compactwise and then
glued: Kollár's resolution of "any analytic space that is an increasing union of its compact
subsets" [Kol07, 44], Bierstone–Milman's relatively quasi-compact open subsets, over each of which
the sequence of blowings-up is finite [BM97, Theorem 1.6 and the remarks after it], and Hironaka's
analytic spaces, "countable at infinity" [Hir64, p. 120] and "a countable increasing union of
relatively compact open subspaces" [Hir64, p. 121].
-/

@[expose] public section

namespace Manifold

open TopologicalSpace Set

variable {M : Type*} [TopologicalSpace M]

/-- The relatively compact open subset `M_n := int K_{n+1}` cut out of the compact exhaustion
`K`, as an open of `M`, so that Mathlib's charted-space and manifold instances on opens apply to
it.-/
def relCompactOpen (K : CompactExhaustion M) (n : ℕ) : Opens M :=
  ⟨interior (K (n + 1)), isOpen_interior⟩

/-! ### The manifold is locally compact and σ-compact -/

section Manifold

variable (E : Type*) [TopologicalSpace E] (M : Type*) [TopologicalSpace M] [ChartedSpace E M]

/-- A charted space modelled on a locally compact space is locally compact (Mathlib's
`ChartedSpace.locallyCompactSpace`).-/
theorem locallyCompactSpace_of_chartedSpace [LocallyCompactSpace E] : LocallyCompactSpace M :=
  ChartedSpace.locallyCompactSpace E M

/-- A second countable charted space modelled on a locally compact space is σ-compact: Hironaka's
"countable at infinity" [Hir64, p. 120] (Mathlib's
`sigmaCompactSpace_of_locallyCompact_secondCountable`).-/
theorem sigmaCompactSpace_of_chartedSpace [LocallyCompactSpace E] [SecondCountableTopology M] :
    SigmaCompactSpace M :=
  haveI := ChartedSpace.locallyCompactSpace E M
  inferInstance

/-- A second countable charted space modelled on a locally compact space admits a compact
exhaustion `K_0 ⊆ int K_1 ⊆ K_1 ⊆ …`, `⋃ K_n = M` (Mathlib's `CompactExhaustion.choice`).-/
theorem nonempty_compactExhaustion [LocallyCompactSpace E] [SecondCountableTopology M] :
    Nonempty (CompactExhaustion M) :=
  haveI := ChartedSpace.locallyCompactSpace E M
  ⟨CompactExhaustion.choice M⟩

end Manifold

section FiniteDimensional

variable (𝕜 : Type) [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (M : Type*) [TopologicalSpace M] [ChartedSpace E M]

end FiniteDimensional

/-! ### The relatively compact opens `M_n := int K_{n+1}` -/

section Exhaustion

variable (K : CompactExhaustion M)

/-- `M_n := int K_{n+1}` as a set.-/
@[simp] theorem coe_relCompactOpen (n : ℕ) :
    (relCompactOpen K n : Set M) = interior (K (n + 1)) := rfl

/-- `closure (int K_{n+1}) ⊆ K_{n+1}`: compact sets are closed in a Hausdorff space.-/
theorem closure_relCompactOpen_subset [T2Space M] (n : ℕ) :
    closure (relCompactOpen K n : Set M) ⊆ K (n + 1) :=
  closure_minimal interior_subset (K.isCompact (n + 1)).isClosed

/-- Each `M_n` is relatively compact: its closure is a closed subset of the compact `K_{n+1}`.-/
theorem isCompact_closure_relCompactOpen [T2Space M] (n : ℕ) :
    IsCompact (closure (relCompactOpen K n : Set M)) :=
  (K.isCompact (n + 1)).of_isClosed_subset isClosed_closure (closure_relCompactOpen_subset K n)

/-- `closure M_n ⊆ M_{n+1}`, i.e. `closure (int K_{n+1}) ⊆ K_{n+1} ⊆ int K_{n+2}`.-/
theorem closure_relCompactOpen_subset_succ [T2Space M] (n : ℕ) :
    closure (relCompactOpen K n : Set M) ⊆ (relCompactOpen K (n + 1) : Set M) :=
  (closure_relCompactOpen_subset K n).trans (K.subset_interior_succ (n + 1))

end Exhaustion

end Manifold
