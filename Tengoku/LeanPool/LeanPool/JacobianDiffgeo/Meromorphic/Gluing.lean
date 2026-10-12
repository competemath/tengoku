/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Meromorphic.GermSpace
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Meromorphic.CodiscreteBridge
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Meromorphic.OrderEval
public import Tengoku

/-!
# Sheaf gluing for `MeroGermOn` (§6.6): the Čech `H⁰` engine

Unit: meromorphic-and-divisors (`docs/design/meromorphic-and-divisors.md` §4.4, proof plan §6.6).

* `MeroGermOn.exists_glue`: compatible germ classes on an open cover glue to a class on the
  union (via the canonical repaired representative `holoRepr`, whose pointwise rigidity —
  `evalAt_restrict` — makes the gluing elementary, no coherence lemma needed).
* `MeroGermOn.glue_unique`: the glued class is unique.
-/

@[expose] public section

open scoped ContDiff Manifold
open Set Filter Topology

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace MeroGermOn

end MeroGermOn

end RS
