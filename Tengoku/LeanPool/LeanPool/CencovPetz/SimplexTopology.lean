/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import Tengoku.LeanPool.LeanPool.CencovPetz.Simplex
public import Tengoku

/-!
# `CencovPetz.SimplexTopology`

Topology on the finite open simplex.

We use the topology induced by the coordinate map `p ↦ p.p : Simplex α → (α → ℝ)`.  Since the
proof fields of `Simplex` are propositions, this agrees with the usual subspace topology.

## Main results

- `CencovPetz.Simplex.continuous_p`
- `CencovPetz.Simplex.continuous_eval`
-/

@[expose] public section

namespace LeanPool.CencovPetz
open scoped BigOperators

universe u

variable {α : Type u} [Fintype α]

namespace Simplex

instance : TopologicalSpace (Simplex α) :=
  TopologicalSpace.induced (fun p : Simplex α => p.p) inferInstance

/--
@isnad1 id=continuo.0h1v.s5.38c7a4e0bec8 from=translated src=- shape=70b645a7 vocab=cfdad245
-/
lemma continuous_p : Continuous fun p : Simplex α => p.p :=
  continuous_induced_dom

/--
@isnad1 id=continuo.0h2v.s4.77d4b77cf5e6 from=translated src=- shape=187d51d6 vocab=cfdad245
-/
lemma continuous_eval (a : α) : Continuous fun p : Simplex α => p.p a :=
  (continuous_apply a).comp continuous_p

end Simplex
end LeanPool.CencovPetz
