/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Composition.Defs
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Combinators.Internal.Generic
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Placement.Internal
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Internal

/-!
# Function composition: first-phase boundary

This module runs the first function machine with its output redirected to the
raw-output work tape, places that run in the composite layout, and exposes the
exact tape facts required by the normalization tail.
-/

public section

namespace Complexity

namespace TM

variable {nf ng : ℕ}

end TM

end Complexity
