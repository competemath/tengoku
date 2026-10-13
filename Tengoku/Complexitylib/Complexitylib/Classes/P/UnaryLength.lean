/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Classes.P.UnaryLength.Internal

/-!
# Polynomial-time unary input length

## Main result

- `unaryLength_mem_FP` — `x ↦ 1^|x|` is polynomial-time computable
-/

public section

namespace Complexity

/-- Writing one unary mark per input bit is a polynomial-time string
function.
@isnad1 id=mem.0h0v.s4.e35d0b0702c0 from=translated src=- shape=c95762a7 vocab=7df7b9db
-/
theorem unaryLength_mem_FP :
    (fun x : List Bool => List.replicate x.length true) ∈ FP :=
  unaryLength_mem_FP_internal

end Complexity
