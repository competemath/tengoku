/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.LaurentTail.TailSpace
public import Tengoku

/-!
# The truncation map `α_D` and `H¹Tail(D)` (laurent-tails, design §2 D3, §4.2)

Unit: laurent-tails (`docs/design/laurent-tails.md`).

* `alphaFinset D f`: a `Finset` witness containing every point where `α_D f`'s tail component is
  possibly nonzero (`D.support` together with `f`'s pole set).
* `alpha`/`alphaL`: Miranda's truncation `α_D : ℳ X → T[D]`, `α_D f`'s class at `p` is the chart
  restriction of `f` mod `ordGe p (-(D p))` — **at every `p`**, not just on the witness Finset
  (`alpha_apply`, exported per `docs/requests/laurent-tails.md`'s serre-duality-tails ask).
* `ker_alphaL_eq_linSys`: Miranda's `L(D) = ker(α_D)` (PDF 192).
* `H1Tail D := T D ⧸ range(alphaL D)`: Miranda's own definition of `H¹(D)` (the comparison to
  `Cech.H1 D` is `Comparison.lean`'s job).
-/

@[expose] public section

open scoped ContDiff Manifold
open Set TopologicalSpace

namespace RS.LaurentTail

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [CompactSpace X] [ConnectedSpace X] [T1Space X] [DecidableEq X]

/-! ### `alphaFinset`, `alpha`, `alphaL` -/

/-! ### `H1Tail D` -/

end RS.LaurentTail
