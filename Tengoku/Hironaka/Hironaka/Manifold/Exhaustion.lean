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
`ChartedSpace.locallyCompactSpace`).
@isnad1 id=locallyc.0h2v.s4.6b7232130eae from=translated src=- shape=f6cd0652 vocab=b81aab21
-/
theorem locallyCompactSpace_of_chartedSpace [LocallyCompactSpace E] : LocallyCompactSpace M :=
  ChartedSpace.locallyCompactSpace E M

/-- A second countable charted space modelled on a locally compact space is σ-compact: Hironaka's
"countable at infinity" [Hir64, p. 120] (Mathlib's
`sigmaCompactSpace_of_locallyCompact_secondCountable`).
@isnad1 id=sigmacom.0h2v.s4.5d6e1d26ae1a from=translated src=- shape=e743e892 vocab=ae0eb1dd
-/
theorem sigmaCompactSpace_of_chartedSpace [LocallyCompactSpace E] [SecondCountableTopology M] :
    SigmaCompactSpace M :=
  haveI := ChartedSpace.locallyCompactSpace E M
  inferInstance

/-- A second countable charted space modelled on a locally compact space admits a compact
exhaustion `K_0 ⊆ int K_1 ⊆ K_1 ⊆ …`, `⋃ K_n = M` (Mathlib's `CompactExhaustion.choice`).
@isnad1 id=nonempty.0h2v.s4.670d86cd715a from=translated src=- shape=f24e7774 vocab=9fc0663d
-/
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

/-- `M_n := int K_{n+1}` as a set.
@isnad1 id=eq.0h3v.s5.c891ad528ccb from=translated src=- shape=8e11a4e6 vocab=244f2240
-/
@[simp] theorem coe_relCompactOpen (n : ℕ) :
    (relCompactOpen K n : Set M) = interior (K (n + 1)) := rfl

/-- `closure (int K_{n+1}) ⊆ K_{n+1}`: compact sets are closed in a Hausdorff space.
@isnad1 id=le.0h3v.s5.fdfc9a8ab411 from=translated src=- shape=2e963a43 vocab=cae4a5d3
-/
theorem closure_relCompactOpen_subset [T2Space M] (n : ℕ) :
    closure (relCompactOpen K n : Set M) ⊆ K (n + 1) :=
  closure_minimal interior_subset (K.isCompact (n + 1)).isClosed

/-- Each `M_n` is relatively compact: its closure is a closed subset of the compact `K_{n+1}`.
@isnad1 id=iscompac.0h3v.s5.628736688106 from=translated src=- shape=762fb01d vocab=f9e0ddb5
-/
theorem isCompact_closure_relCompactOpen [T2Space M] (n : ℕ) :
    IsCompact (closure (relCompactOpen K n : Set M)) :=
  (K.isCompact (n + 1)).of_isClosed_subset isClosed_closure (closure_relCompactOpen_subset K n)

/-- `closure M_n ⊆ M_{n+1}`, i.e. `closure (int K_{n+1}) ⊆ K_{n+1} ⊆ int K_{n+2}`.
@isnad1 id=le.0h3v.s5.1d197541d41b from=translated src=- shape=16384d03 vocab=409ae971
-/
theorem closure_relCompactOpen_subset_succ [T2Space M] (n : ℕ) :
    closure (relCompactOpen K n : Set M) ⊆ (relCompactOpen K (n + 1) : Set M) :=
  (closure_relCompactOpen_subset K n).trans (K.subset_interior_succ (n + 1))

end Exhaustion

end Manifold
