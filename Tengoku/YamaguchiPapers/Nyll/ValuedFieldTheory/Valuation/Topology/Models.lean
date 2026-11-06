/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.Topology.Homeomorph.Defs
import Tengoku.Seed.Topology.WithTopology

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Topological API for `WithTopology`

This file adds only the two topology lemmas used by valuation theory. The
underlying type, topology, and basic API come directly from Mathlib. Algebraic
structures needed on a particular topology-indexed copy are installed at that
copy's owner rather than globally in the root `WithTopology` namespace.
-/

universe u v

namespace WithTopology

variable {X : Type u} {t : TopologicalSpace X}

/-- The canonical homeomorphism from Mathlib's topology-indexed copy to its
underlying carrier equipped with the indexed topology.-/
def homeomorph {α : Type u} {topology : TopologicalSpace α} :
    @Homeomorph (WithTopology α topology) α
      (inferInstance : TopologicalSpace (WithTopology α topology)) topology where
  toEquiv := WithTopology.equiv α topology
  continuous_toFun := continuous_ofTopology topology
  continuous_invFun := continuous_toTopology topology

end WithTopology
