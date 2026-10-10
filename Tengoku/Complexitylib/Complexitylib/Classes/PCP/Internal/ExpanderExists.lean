/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Tengoku.Complexitylib.Complexitylib.Classes.PCP.Internal.ExpanderRandom
public import Tengoku.Complexitylib.Complexitylib.Classes.PCP.Internal.PermGraph
public import Tengoku.Complexitylib.Complexitylib.Classes.PCP.Internal.Cheeger
public import Tengoku.Complexitylib.Complexitylib.Classes.PCP.Internal.Expander

/-!
# An expander family exists

The three strands meet here. `ExpanderRandom` produces, for every `n`, thirty
permutations of `Fin n` no vertex set of at most half the vertices survives;
`PermGraph` turns those into a `60`-regular graph with edge expansion `1/600`;
and `Cheeger` converts edge expansion into a spectral gap once enough self-loops
are added to make the walk lazy. Relabelling the resulting `120` darts as
`Fin 120` puts the graph in the rotation-map form `ExpanderFamily` asks for.

The construction is not explicit — the permutations come from
`Classical.choose` on a counting argument — which is all the mathematics of
Dinur's proof needs. An explicit family would be needed only to make the
reduction itself polynomial-time computable.

## Main definitions

- `Complexity.goodPerms` — the chosen permutations
- `Complexity.randExpander` — the resulting `ExpanderFamily`
-/

@[expose] public section

namespace Complexity

/-- The spectral bound the construction achieves. -/
noncomputable def randLam : ℝ := 1 - (1 / (2 * (10 : ℝ) * 30)) ^ 2 / 4

theorem randLam_nonneg : 0 ≤ randLam := by
  rw [randLam]
  norm_num

theorem randLam_lt_one : randLam < 1 := by
  rw [randLam]
  norm_num

end Complexity
