/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.SAT.Tseitin.Internal.Streaming
public import Tengoku.Complexitylib.Complexitylib.SAT.Tseitin.Machine.Controller
public import Tengoku.Complexitylib.Complexitylib.SAT.Tseitin.Machine.Internal.BufferSpecs

/-!
# Register invariant for the Tseitin streaming controller

This file connects the pure token transducer in `ThreeSAT.Streaming` to the
finite control and six unary registers of `validEmitterTM`. It deliberately
contains no execution simulation. The definitions here only say how a pure
streaming state is represented:

- pending literals retain their signs in `PendingSigns`;
- the parser scan becomes a `StreamMode`;
- unbounded variable indices occupy `freshReg`, `currentReg`, and the three
  pending-literal registers;
- the scratch register is zero; and
- the output tape is an append-only `TM.OutAcc` containing the encoding of
  the already-emitted tokens.

The projection and parked-tape lemmas are the glue needed to instantiate the
register-level Hoare specifications in `Machine.Internal.BufferSpecs`.

## Main definitions

- `PendingSigns.ofStreaming`
- `StreamMode.ofStreaming`
- `StreamMode.ofState`
- `BufferValues.ofStreaming`
- `StreamingStatePred`
-/

@[expose] public section

namespace Complexity

namespace SAT

namespace ThreeSAT

namespace Machine

/-! ## Finite-control representation -/

/-- Forget the variable indices of a pure pending window, retaining exactly
the signs kept by the machine controller. -/
@[simp] def PendingSigns.ofStreaming : Streaming.Pending → PendingSigns
  | .zero => .zero
  | .one a => .one a.sign
  | .two a b => .two a.sign b.sign
  | .three a b c => .three a.sign b.sign c.sign

/-- Convert a pure parser scan to its finite controller mode under the signs
of the current pending window. -/
@[simp] def StreamMode.ofStreaming
    (pending : Streaming.Pending) : Streaming.Scan → StreamMode
  | .boundary => .boundary (PendingSigns.ofStreaming pending)
  | .literal sign _ => .literal (PendingSigns.ofStreaming pending) sign

/-- Finite controller mode represented by a complete pure streaming state. -/
def StreamMode.ofState (st : Streaming.State) : StreamMode :=
  .ofStreaming st.pending st.scan

/--
@isnad1 id=eq.0h4v.s4.a5d926f0ef55 from=translated src=- shape=49000b39 vocab=f93a1924
-/
@[simp] theorem StreamMode.ofState_mk (next : ℕ) (pending : Streaming.Pending)
    (scan : Streaming.Scan) (emitted : List EncToken) :
    StreamMode.ofState ⟨next, pending, scan, emitted⟩ =
      StreamMode.ofStreaming pending scan := rfl

/-- Sign control after a pure literal push agrees with `PendingSigns.push`.
@isnad1 id=eq.0h2v.s4.7d0ee7dcb1a2 from=translated src=- shape=c0fce23d vocab=e6907831
-/
theorem PendingSigns.ofStreaming_pushLiteral
    (st : Streaming.State) (lit : Lit) :
    PendingSigns.ofStreaming (Streaming.pushLiteral st lit).pending =
      (PendingSigns.ofStreaming st.pending).push lit.sign := by
  cases st with
  | mk next pending scan emitted =>
      cases pending <;> rfl

/-- A pure literal push returns the parser to the corresponding boundary
mode.
@isnad1 id=eq.0h2v.s4.d3d16b84a35d from=translated src=- shape=0c18b396 vocab=23913931
-/
@[simp] theorem StreamMode.ofState_pushLiteral
    (st : Streaming.State) (lit : Lit) :
    StreamMode.ofState (Streaming.pushLiteral st lit) =
      .boundary ((PendingSigns.ofStreaming st.pending).push lit.sign) := by
  cases st with
  | mk next pending scan emitted =>
      cases pending <;> rfl

/-- Closing a pure clause resets both pending signs and parser mode.
@isnad1 id=eq.0h1v.s3.9867a67e114f from=translated src=- shape=81aed124 vocab=1f5de0b6
-/
@[simp] theorem StreamMode.ofState_closeClause (st : Streaming.State) :
    StreamMode.ofState (Streaming.closeClause st) = .boundary .zero := by
  cases st
  rfl

/-! ## Unary-register representation -/

/-- Unary value stored in `currentReg` for a pure parser scan. -/
@[simp] def streamingScanValue : Streaming.Scan → ℕ
  | .boundary => 0
  | .literal _ var => var

/-- Unary value stored in `bufferAReg` for a pending window. -/
@[simp] def streamingBufferA : Streaming.Pending → ℕ
  | .zero => 0
  | .one a => a.var
  | .two a _ => a.var
  | .three a _ _ => a.var

/-- Unary value stored in `bufferBReg` for a pending window. -/
@[simp] def streamingBufferB : Streaming.Pending → ℕ
  | .zero => 0
  | .one _ => 0
  | .two _ b => b.var
  | .three _ b _ => b.var

/-- Unary value stored in `bufferCReg` for a pending window. -/
@[simp] def streamingBufferC : Streaming.Pending → ℕ
  | .zero => 0
  | .one _ => 0
  | .two _ _ => 0
  | .three _ _ c => c.var

/-- Six unary-register values representing a pure streaming state. -/
def BufferValues.ofStreaming (st : Streaming.State) : BufferValues :=
  { fresh := st.next
    current := streamingScanValue st.scan
    a := streamingBufferA st.pending
    b := streamingBufferB st.pending
    c := streamingBufferC st.pending
    scratch := 0 }

/--
@isnad1 id=eq.0h1v.s3.41b5839a0e65 from=translated src=- shape=7718e021 vocab=0ff2c780
-/
@[simp] theorem BufferValues.ofStreaming_fresh (st : Streaming.State) :
    (BufferValues.ofStreaming st).fresh = st.next := rfl

/--
@isnad1 id=eq.0h1v.s3.dbe05f6c113f from=translated src=- shape=7367b1cd vocab=7574d9f9
-/
@[simp] theorem BufferValues.ofStreaming_current (st : Streaming.State) :
    (BufferValues.ofStreaming st).current = streamingScanValue st.scan := rfl

/--
@isnad1 id=eq.0h1v.s3.c9027115e10f from=translated src=- shape=7367b1cd vocab=879a0034
-/
@[simp] theorem BufferValues.ofStreaming_a (st : Streaming.State) :
    (BufferValues.ofStreaming st).a = streamingBufferA st.pending := rfl

/--
@isnad1 id=eq.0h1v.s3.fcc6e4953b0b from=translated src=- shape=7367b1cd vocab=176a17cf
-/
@[simp] theorem BufferValues.ofStreaming_b (st : Streaming.State) :
    (BufferValues.ofStreaming st).b = streamingBufferB st.pending := rfl

/--
@isnad1 id=eq.0h1v.s3.dcb188e587c6 from=translated src=- shape=7367b1cd vocab=64ea7849
-/
@[simp] theorem BufferValues.ofStreaming_c (st : Streaming.State) :
    (BufferValues.ofStreaming st).c = streamingBufferC st.pending := rfl

/--
@isnad1 id=eq.0h1v.s3.9c68dca760c4 from=translated src=- shape=f6b6ad72 vocab=10a48c07
-/
@[simp] theorem BufferValues.ofStreaming_scratch (st : Streaming.State) :
    (BufferValues.ofStreaming st).scratch = 0 := rfl

/-- Every register tape in the representation of a pure state is parked.
@isnad1 id=parked.0h2v.s3.cf051e8c428c from=translated src=- shape=bc71e401 vocab=09ee8995
-/
theorem BufferValues.ofStreaming_work_parked (st : Streaming.State) :
    ∀ i, TM.Parked ((BufferValues.ofStreaming st).work i) :=
  (BufferValues.ofStreaming st).work_parked

/-! ## Complete tape predicate -/

/-- Tape-level representation of a pure streaming state. The input tape is a
fixed parked ghost for buffer operations; the work tapes are its six unary
registers; and the output accumulator contains exactly the emitted tokens. -/
def StreamingStatePred (inp : Tape) (st : Streaming.State) :
    TapePred workTapeCount :=
  BufferPred inp (BufferValues.ofStreaming st) (encodeTokens st.emitted)

/--
@isnad1 id=eq.0h2v.s4.5ab22b020e26 from=translated src=- shape=174e6670 vocab=465d9fb0
-/
@[simp] theorem streamingStatePred_eq_bufferPred (inp : Tape)
    (st : Streaming.State) :
    StreamingStatePred inp st =
      BufferPred inp (BufferValues.ofStreaming st) (encodeTokens st.emitted) := rfl

namespace StreamingStatePred

variable {inp actualInput out : Tape} {st : Streaming.State}
  {work : Fin workTapeCount → Tape}

/-- Project the fixed input tape from the streaming-state predicate.
@isnad1 id=eq.0h6v.s4.cba9a40b4fde from=translated src=- shape=efb765a1 vocab=3404d8bc
-/
theorem input_eq (h : StreamingStatePred inp st actualInput work out) :
    actualInput = inp :=
  h.1

/-- Project the six-register work-tape function.
@isnad1 id=eq.0h6v.s4.2d4e967e6fb1 from=translated src=- shape=60221a53 vocab=26aad08d
-/
theorem work_eq (h : StreamingStatePred inp st actualInput work out) :
    work = (BufferValues.ofStreaming st).work :=
  h.2.1

/-- Project the exact append-only encoded-token accumulator.
@isnad1 id=outacc.0h6v.s4.5de8bf449d23 from=translated src=- shape=03b1861f vocab=9b70cbc9
-/
theorem outAcc (h : StreamingStatePred inp st actualInput work out) :
    TM.OutAcc (encodeTokens st.emitted) out :=
  h.2.2

/-- The represented input is parked whenever its fixed ghost is parked.
@isnad1 id=parked.1h6v.s4.99117e6c8a95 from=translated src=- shape=e926dd98 vocab=047c3c50
-/
theorem input_parked (h : StreamingStatePred inp st actualInput work out)
    (hinp : TM.Parked inp) : TM.Parked actualInput := by
  rw [input_eq h]
  exact hinp

/-- Every represented work tape is parked.
@isnad1 id=parked.0h7v.s4.41391672417d from=translated src=- shape=c07d7ceb vocab=047c3c50
-/
theorem work_parked (h : StreamingStatePred inp st actualInput work out) :
    ∀ i, TM.Parked (work i) := by
  rw [work_eq h]
  exact BufferValues.ofStreaming_work_parked st

/-- The represented output accumulator is parked.
@isnad1 id=parked.0h6v.s4.b5c7a10d563d from=translated src=- shape=e922a199 vocab=047c3c50
-/
theorem output_parked (h : StreamingStatePred inp st actualInput work out) :
    TM.Parked out :=
  (outAcc h).parked

/-- Project the fresh-variable register.
@isnad1 id=eq.0h6v.s4.a5b65dd6117d from=translated src=- shape=9b2569a8 vocab=65d075f7
-/
theorem work_fresh (h : StreamingStatePred inp st actualInput work out) :
    work freshReg = TM.regTape st.next := by
  rw [work_eq h]
  simp

/-- Project the current-literal register.
@isnad1 id=eq.0h6v.s4.be1737e2e8db from=translated src=- shape=a89e72a8 vocab=f2963c1c
-/
theorem work_current (h : StreamingStatePred inp st actualInput work out) :
    work currentReg = TM.regTape (streamingScanValue st.scan) := by
  rw [work_eq h]
  simp

/-- Project the first pending-literal register.
@isnad1 id=eq.0h6v.s4.2b40b832f6d4 from=translated src=- shape=a89e72a8 vocab=c889a492
-/
theorem work_a (h : StreamingStatePred inp st actualInput work out) :
    work bufferAReg = TM.regTape (streamingBufferA st.pending) := by
  rw [work_eq h]
  simp

/-- Project the second pending-literal register.
@isnad1 id=eq.0h6v.s4.67c9850eee10 from=translated src=- shape=a89e72a8 vocab=ecf60729
-/
theorem work_b (h : StreamingStatePred inp st actualInput work out) :
    work bufferBReg = TM.regTape (streamingBufferB st.pending) := by
  rw [work_eq h]
  simp

/-- Project the third pending-literal register.
@isnad1 id=eq.0h6v.s4.15c4b86b274c from=translated src=- shape=a89e72a8 vocab=1a478740
-/
theorem work_c (h : StreamingStatePred inp st actualInput work out) :
    work bufferCReg = TM.regTape (streamingBufferC st.pending) := by
  rw [work_eq h]
  simp

/-- Project the zero scratch register.
@isnad1 id=eq.0h6v.s4.87155eca0dd5 from=translated src=- shape=dee0e1b0 vocab=5fea746c
-/
theorem work_scratch (h : StreamingStatePred inp st actualInput work out) :
    work scratchReg = TM.regTape 0 := by
  rw [work_eq h]
  simp

end StreamingStatePred

end Machine

end ThreeSAT

end SAT

end Complexity
