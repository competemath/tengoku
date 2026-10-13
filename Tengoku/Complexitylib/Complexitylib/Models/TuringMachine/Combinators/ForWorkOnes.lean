/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Combinators.ForWorkOnes.Defs
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Combinators.ForWorkOnes.Internal

/-!
# One-prefix work-tape loop combinator

`TM.forWorkOnesTM driverIdx body` consumes a consecutive prefix of `1` symbols
from a work tape and invokes `body` once per symbol. It halts on the first
non-`1` without consuming it. This is the concrete unary-width driver used by
the RAM snapshot word decoder.

## Main results

- `TM.ForWorkOnesLoopSpec.reachesIn` composes an indexed exact-execution
  certificate for the full loop.
- `TM.IsTransducer.forWorkOnesTM` preserves one-way output safety.
-/

public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Exact remaining execution of a certified consecutive-one work loop.
@isnad1 id=reachesi.1h8v.s5.586bb314e922 from=translated src=- shape=f2bc5e27 vocab=2ecd1a46
-/
theorem ForWorkOnesLoopSpec.reachesIn
    {driverIdx : Fin n} {body : TM n} {bodyTime : ℕ → ℕ}
    {total count value : ℕ}
    (spec : ForWorkOnesLoopSpec driverIdx body bodyTime total)
    (htotal : value + count = total) :
    (forWorkOnesTM driverIdx body).reachesIn
      (forWorkOnesLoopTime bodyTime value count)
      (spec.scanCfg value) spec.doneCfg :=
  spec.reachesIn_internal count value htotal

/-- Iterating a one-way-output body over a one-prefix remains a transducer.
@isnad1 id=istransd.1h3v.s4.3c5c14440a10 from=translated src=- shape=88a9cf5b vocab=3ceb04c5
-/
theorem IsTransducer.forWorkOnesTM
    {driverIdx : Fin n} {body : TM n} (hbody : body.IsTransducer) :
    (forWorkOnesTM driverIdx body).IsTransducer :=
  hbody.forWorkOnesTM_internal

end TM

end Complexity
