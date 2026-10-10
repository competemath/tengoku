/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Composition.Internal.FirstPhase
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Composition.Internal.Tail
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.OutputBounds

/-!
# Sequential composition correctness — proof internals

This module connects the first function computation's placed raw-output
boundary to the normalization tail. It derives coarse monotone time bounds for
both function composition and preprocessing followed by a language decider.
-/

public section

namespace Complexity

namespace TM

variable {nf ng : ℕ}

end TM

end Complexity
