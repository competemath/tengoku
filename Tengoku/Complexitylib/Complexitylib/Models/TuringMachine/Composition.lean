/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Composition.Defs
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Composition.Internal

/-!
# Sequential composition after function computation

`TM.compositionTM tmF tmG` is an executable deterministic machine that runs
`tmF`, copies its delimited output onto a fresh virtual-input tape, and then
runs `tmG` on that output. Work tapes of the two machines occupy disjoint
blocks, and the intermediate raw output may contain arbitrary junk after its
first delimiter.

## Main result

- `TM.compositionTM_computesInTime` — correctness with a monotone coarse time bound
- `TM.compositionTM_decidesInTime` — function computation followed by a decider
-/

public section

namespace Complexity

namespace TM

variable {nf ng : ℕ}

end TM

end Complexity
