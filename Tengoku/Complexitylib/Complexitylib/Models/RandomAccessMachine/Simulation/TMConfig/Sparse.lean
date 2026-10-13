/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.Defs
public import Tengoku.Complexitylib.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.Internal

/-!
# Sparse unbounded TM configurations in RAM registers

This is the fixed-layout representation used for the uniform TM-to-RAM
simulation. Unlike the bounded dense layout, its addresses do not depend on an
input length or running-time bound.
-/

public section

namespace Complexity

namespace RAM

namespace TMConfig

namespace Sparse

/-- Distinct sparse fields occupy distinct RAM registers.
@isnad1 id=injectiv.0h1v.s3.32cce1cceb51 from=translated src=- shape=9ef37d6b vocab=488308a5
-/
theorem fieldReg_injective : Function.Injective (@fieldReg n) :=
  fieldReg_injective_internal

/-- The canonical sparse encoding represents every state, head, and cell.
@isnad1 id=represen.0h3v.s4.483e081d406d from=translated src=- shape=176c88a0 vocab=a5738c80
-/
theorem encodeRegs_represents (tm : TM n) (cfg : Complexity.Cfg n tm.Q) :
    Represents tm cfg (encodeRegs tm cfg) :=
  encodeRegs_represents_internal tm cfg

/-- Any representing sparse store decodes to its complete configuration; no
external cell-window premise is needed.
@isnad1 id=eq.1h4v.s4.aeed8c33efae from=translated src=- shape=722246ec vocab=b2947fe7
-/
theorem decode_of_represents (tm : TM n) (cfg : Complexity.Cfg n tm.Q)
    (store : Structured.Store) (hrepresents : Represents tm cfg store) :
    decode tm store = cfg :=
  decode_of_represents_internal tm cfg store hrepresents

/-- Sparse encoding followed by decoding is exact for every configuration.
@isnad1 id=eq.0h3v.s4.a20c141229b9 from=translated src=- shape=09807c37 vocab=50ca22c3
-/
theorem decode_encode (tm : TM n) (cfg : Complexity.Cfg n tm.Q) :
    decode tm (encodeRegs tm cfg) = cfg :=
  decode_encode_internal tm cfg

end Sparse

end TMConfig

end RAM

end Complexity
