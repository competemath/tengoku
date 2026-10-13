/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Combinators.ForInput.Defs
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Combinators.ForInput.Internal

/-!
# Read-only-input loop combinator

`TM.forInputTM body` advances over a Boolean input symbol and invokes `body`
without copying the input into auxiliary space. For input-preserving bodies,
this iterates exactly once per original symbol. It is the input-fueled
counterpart of the unary-work-register loop `TM.forRegTM`.

## Main results

- `TM.IsTransducer.forInputTM` — input-driven iteration preserves one-way output.
- `TM.ForInputLoopSpec.reachesIn` — exact indexed execution from a loop certificate.
- `TM.ForInputLoopSpaceSpec.prefix_withinAuxSpace` — every prefix of the exact
  loop run respects the certified auxiliary-space budget.
-/

public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Exact remaining execution of a certified input-driven loop.
@isnad1 id=reachesi.1h7v.s5.cc50c770371b from=translated src=- shape=d05d7dec vocab=f5168474
-/
theorem ForInputLoopSpec.reachesIn {body : TM n} {bodyTime : ℕ → ℕ}
    {total count value : ℕ} (spec : ForInputLoopSpec body bodyTime total)
    (htotal : value + count = total) :
    (forInputTM body).reachesIn (forInputLoopTime bodyTime value count)
      (spec.scanCfg value) spec.doneCfg :=
  spec.reachesIn_internal count value htotal

/-- Every prefix up to the exact remaining runtime of a certified input-driven
loop respects its all-reachable auxiliary-space budget.
@isnad1 id=withinau.4h11v.s6.1f7f9861bb38 from=translated src=- shape=b780a172 vocab=6c620512
-/
theorem ForInputLoopSpaceSpec.prefix_withinAuxSpace
    {body : TM n} {bodyTime : ℕ → ℕ}
    {total inputLength spaceBound count value t : ℕ}
    {spec : ForInputLoopSpec body bodyTime total}
    (spaceSpec : ForInputLoopSpaceSpec spec inputLength spaceBound)
    {c : Cfg n (forInputTM body).Q}
    (htotal : value + count = total)
    (hreach : (forInputTM body).reachesIn t (spec.scanCfg value) c)
    (htime : t ≤ forInputLoopTime bodyTime value count) :
    c.WithinAuxSpace inputLength spaceBound :=
  spaceSpec.prefix_withinAuxSpace_internal count value t c htotal hreach htime

/-- Iterating a one-way-output body over the read-only input remains a
one-way-output transducer.
@isnad1 id=istransd.1h2v.s3.bc1387846203 from=translated src=- shape=525138f7 vocab=501efa89
-/
theorem IsTransducer.forInputTM {n : ℕ} {body : TM n}
    (hbody : body.IsTransducer) : (forInputTM body).IsTransducer :=
  hbody.forInputTM_internal

end TM

end Complexity
