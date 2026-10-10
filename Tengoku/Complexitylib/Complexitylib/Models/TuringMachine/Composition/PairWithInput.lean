/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Composition.PairWithInput.Defs
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Composition.PairWithInput.Internal

/-!
# Pair a computed value with the original input

This module exposes a generic deterministic fanout combinator. If `tmF`
computes `f`, then `pairWithInputTM tmF` computes `x ↦ pair (f x) x` while
retaining a concrete polynomial-preserving time bound.

## Main result

- `TM.pairWithInputTM_computesInTime` — computation paired with original input
-/

public section

namespace Complexity

namespace TM

variable {nf : ℕ}

end TM

end Complexity
