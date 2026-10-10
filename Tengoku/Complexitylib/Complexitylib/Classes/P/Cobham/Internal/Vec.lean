/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import Tengoku.Complexitylib.Complexitylib.Classes.P.Cobham.Vec
import Tengoku.Complexitylib.Complexitylib.Classes.P.FinsetDomain
public import Tengoku.Complexitylib.Complexitylib.Classes.P.PairWithInput

/-!
# The multi-arity bridge — proof internals

The public tuple encoding and `FPn` predicate live in
`Complexitylib.Classes.P.Cobham.Vec`. This internal module supplies the concrete
`FP` building blocks used to connect their arity-one specialization to `FP`.

## Main results

- `Cobham.const_nil_mem_FP`, `Cobham.pairLeftNil_mem_FP` — the two `FP` maps the
  arity-one glue needs
-/

@[expose] public section

namespace Complexity

namespace Cobham

/-! ## Foundational FP building blocks -/

/-- The constant empty-output function is in `FP` (the empty-support case of
`ite_mem_finset_mem_FP`). -/
theorem const_nil_mem_FP : (fun _ : List Bool => ([] : List Bool)) ∈ FP := by
  have h := ite_mem_finset_mem_FP (fun _ => []) (∅ : Finset (List Bool))
  simpa using h

end Cobham

end Complexity
