/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Tengoku

/-!
# Facts about straight-line programs

Upstreaming candidates for `Cslib.Computability.Circuit.Program`:

* `Program.lines_wires_eq_gate_lt`: a gate reads only earlier gates.
* `Program.FanInAtMost.arity_le`: under a fan-in bound, every line has bounded arity.
* `Program.trace_gate`: the value of a gate is its operation applied to the values of its
  arguments.
* `Program.Upstream` and `Program.trace_congr_of_upstream`: the value of a wire depends only
  on the inputs upstream of it.
* `Circuit.innerSize`: the number of gates of positive arity. Gates of arity zero are
  constants, leaves of the circuit like its inputs.
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {n s : ℕ}

end Cslib.Circuits
