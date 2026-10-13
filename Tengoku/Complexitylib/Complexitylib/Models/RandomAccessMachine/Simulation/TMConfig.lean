/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Defs
public import Tengoku.Complexitylib.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Internal

/-!
# Bounded Turing-machine configurations in RAM registers

This module exposes the first representation layer of the Turing-machine to RAM
simulation. The register layout is explicit, blank cells use value zero, and
`decode_encode` states the exact condition under which bounded decoding loses no
information.
-/

public section

namespace Complexity

namespace RAM

namespace TMConfig

/-- The state field is register zero.
@isnad1 id=eq.0h2v.s4.3559e0a59bb8 from=translated src=- shape=515d1a8c vocab=27edd30b
-/
@[simp] theorem fieldReg_state :
    fieldReg (stateField (n := n) (bound := bound)) = 0 :=
  fieldReg_state_internal

/-- Head registers immediately follow the state, in input/work/output order.
@isnad1 id=eq.0h3v.s5.1961c2cbd9c1 from=translated src=- shape=3b4ccabb vocab=fbf7afbe
-/
@[simp] theorem fieldReg_head (tape : Fin (n + 2)) :
    fieldReg (headField (bound := bound) tape) = 1 + tape.val :=
  fieldReg_head_internal tape

/-- Cell blocks follow all head registers, ordered by tape and position.
@isnad1 id=eq.0h4v.s7.5e7d93f370ee from=translated src=- shape=21a84a7e vocab=12f331b1
-/
@[simp] theorem fieldReg_cell (tape : Fin (n + 2))
    (position : Fin (bound + 1)) :
    fieldReg (cellField tape position) =
      1 + (n + 2) + tape.val * (bound + 1) + position.val :=
  fieldReg_cell_internal tape position

/-- Symbol coding is lossless on the four-symbol tape alphabet.
@isnad1 id=eq.0h1v.s3.13fe149fa7a9 from=translated src=- shape=47dcad53 vocab=e5b95926
-/
theorem symbolDecode_code (symbol : Γ) :
    symbolDecode (symbolCode symbol) = symbol :=
  symbolDecode_code_internal symbol

/-- Canonical finite-state coding is lossless.
@isnad1 id=eq.0h3v.s4.e9f2617f4deb from=translated src=- shape=9a6007cb vocab=aecfe2bd
-/
theorem stateDecode_code (tm : TM n) (state : tm.Q) :
    stateDecode tm (stateCode tm state) = state :=
  stateDecode_code_internal tm state

/-- Reading an encoded field returns exactly that field's value.
@isnad1 id=eq.0h5v.s5.4938dc719b6b from=translated src=- shape=7d3b08de vocab=b71c4d7b
-/
theorem encodeRegs_field (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) (field : Field n bound) :
    encodeRegs tm bound cfg (fieldReg field) = fieldValue tm bound cfg field :=
  encodeRegs_field_internal tm bound cfg field

/-- Every field address lies inside the explicit configuration prefix.
@isnad1 id=lt.0h3v.s4.3d086c044334 from=translated src=- shape=cdc6fac2 vocab=8e04350a
-/
theorem fieldReg_lt (field : Field n bound) :
    fieldReg field < registerCount n bound :=
  fieldReg_lt_internal field

/-- Distinct configuration fields occupy distinct registers.
@isnad1 id=injectiv.0h2v.s3.e45da644d67e from=translated src=- shape=a3f091f9 vocab=bc8650dd
-/
theorem fieldReg_injective : Function.Injective (@fieldReg n bound) :=
  fieldReg_injective_internal

/-- Updating a scratch register beyond the configuration prefix preserves every
represented field.
@isnad1 id=represen.2h7v.s5.33e7cd75838a from=translated src=- shape=29660fff vocab=5eed5e73
-/
theorem Represents.update_outside {tm : TM n} {bound reg value : ℕ}
    {cfg : Complexity.Cfg n tm.Q} {regs : ℕ → ℕ}
    (hrepresents : Represents tm bound cfg regs)
    (hreg : registerCount n bound ≤ reg) :
    Represents tm bound cfg (Function.update regs reg value) :=
  hrepresents.update_outside_internal hreg

/-- The canonical bounded encoding represents every one of its fields.
@isnad1 id=represen.0h4v.s4.029831086e1a from=translated src=- shape=e1b49d5e vocab=93c7d2db
-/
theorem encodeRegs_represents (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) :
    Represents tm bound cfg (encodeRegs tm bound cfg) :=
  encodeRegs_represents_internal tm bound cfg

/-- Any representing store decodes to its configuration when the omitted tape
suffixes are blank. Scratch registers do not affect decoding.
@isnad1 id=eq.2h5v.s5.436d60d2593b from=translated src=- shape=94c425ba vocab=3e0d3de4
-/
theorem decode_of_represents (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) (regs : ℕ → ℕ)
    (hrepresents : Represents tm bound cfg regs)
    (hbounded : Bounded cfg bound) : decode tm bound regs = cfg :=
  decode_of_represents_internal tm bound cfg regs hrepresents hbounded

/-- Decoding an encoded bounded configuration recovers it exactly.
@isnad1 id=eq.1h4v.s5.39f386e2b7ac from=translated src=- shape=4f6e2a7a vocab=63652974
-/
theorem decode_encode (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) (hbounded : Bounded cfg bound) :
    decode tm bound (encode tm bound cfg).regs = cfg :=
  decode_encode_internal tm bound cfg hbounded

/-- Registers beyond the explicit bounded layout are zero.
@isnad1 id=eq.1h5v.s5.86c19ada1f74 from=translated src=- shape=3e639e0e vocab=5aac81bc
-/
theorem encodeRegs_outside (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) {reg : ℕ}
    (hreg : registerCount n bound ≤ reg) :
    encodeRegs tm bound cfg reg = 0 :=
  encodeRegs_outside_internal tm bound cfg hreg

end TMConfig

end RAM

end Complexity
