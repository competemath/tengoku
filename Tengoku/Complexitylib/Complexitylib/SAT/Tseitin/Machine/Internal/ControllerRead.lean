/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.SAT.Tseitin.Machine.Internal.ControllerLift

/-!
# Concrete read paths for the Tseitin streaming controller

This file proves the input-reader plumbing of `validEmitterTM`. Every SAT
token occupies two input bits. Starting in a first-bit read state, the
controller reads those bits in exactly two steps, advances the input head
twice, and reaches the state selected by `scheduleToken`; parked work and
output tapes are unchanged. A first-bit read of the trailing blank reaches
`controllerDone` in one step with all tapes unchanged.

The scheduled state is not interpreted here. Child execution and pure token
semantics remain separate layers.

## Main results

- `validEmitterTM_read_token_reachesIn_internal`
- `validEmitterTM_read_blank_step_internal`
- `validEmitterTM_read_blank_reachesIn_internal`
-/

@[expose] public section

namespace Complexity

namespace SAT

namespace ThreeSAT

namespace Machine

/-! ## Token-bit framing -/

/-- First concrete bit of a SAT encoding token. -/
@[simp] def tokenFirstBit : EncToken → Bool
  | .bit b => b
  | .litSep => false
  | .clauseSep => true

/-- Second concrete bit of a SAT encoding token. -/
@[simp] def tokenSecondBit : EncToken → Bool
  | .bit b => b
  | .litSep => true
  | .clauseSep => false

/-- The named token bits are exactly the existing concrete token encoding.
@isnad1 id=eq.0h1v.s4.9c0bac86028e from=translated src=- shape=c30433b6 vocab=18b73cf6
-/
@[simp] theorem token_encode_eq_bits (tok : EncToken) :
    tok.encode = [tokenFirstBit tok, tokenSecondBit tok] := by
  cases tok with
  | bit b => cases b <;> rfl
  | litSep => rfl
  | clauseSep => rfl

/-- Decoding the two named encoding bits recovers the token.
@isnad1 id=eq.0h1v.s3.312e870c1408 from=translated src=- shape=4eb47a10 vocab=6e98ad39
-/
theorem tokenOfPair_token_bits (tok : EncToken) :
    tokenOfPair (tokenFirstBit tok) (tokenSecondBit tok) = tok := by
  cases tok with
  | bit b => cases b <;> rfl
  | litSep => rfl
  | clauseSep => rfl

/-- The input head and its right neighbor contain the encoding of `tok`. -/
def InputTokenAt (input : Tape) (tok : EncToken) : Prop :=
  input.read = Γ.ofBool (tokenFirstBit tok) ∧
    (input.move .right).read = Γ.ofBool (tokenSecondBit tok)

/-! ## Read configurations -/

/-- Controller configuration after reading the first bit of a token. -/
def controllerSecondCfg {Q : Type} (mode : StreamMode) (first : Bool)
    (c : Cfg workTapeCount Q) : Cfg workTapeCount validEmitterTM.Q where
  state := controllerRead (.second mode first)
  input := c.input.move .right
  work := c.work
  output := c.output

/-- Controller configuration after reading a complete token. -/
def controllerScheduledCfg {Q : Type} (mode : StreamMode) (tok : EncToken)
    (c : Cfg workTapeCount Q) : Cfg workTapeCount validEmitterTM.Q where
  state := scheduleToken mode tok
  input := (c.input.move .right).move .right
  work := c.work
  output := c.output

/-- Halting controller configuration that shares all tapes with `c`. -/
def controllerDoneCfg {Q : Type}
    (c : Cfg workTapeCount Q) : Cfg workTapeCount validEmitterTM.Q where
  state := controllerDone
  input := c.input
  work := c.work
  output := c.output

/--
@isnad1 id=eq.0h4v.s5.9d3106b38ff5 from=translated src=- shape=da601be6 vocab=8b9a028e
-/
@[simp] theorem controllerScheduledCfg_input_head {Q : Type}
    (mode : StreamMode) (tok : EncToken) (c : Cfg workTapeCount Q) :
    (controllerScheduledCfg mode tok c).input.head = c.input.head + 2 := by
  simp [controllerScheduledCfg, Tape.move]

/--
@isnad1 id=eq.0h4v.s4.7d3ff8ffc875 from=translated src=- shape=69b05a07 vocab=936cd9a1
-/
@[simp] theorem controllerScheduledCfg_input_cells {Q : Type}
    (mode : StreamMode) (tok : EncToken) (c : Cfg workTapeCount Q) :
    (controllerScheduledCfg mode tok c).input.cells = c.input.cells := by
  simp [controllerScheduledCfg, Tape.move]

/--
@isnad1 id=eq.0h4v.s4.77a54d54ae81 from=translated src=- shape=495ed757 vocab=7059bbcc
-/
@[simp] theorem controllerScheduledCfg_work {Q : Type}
    (mode : StreamMode) (tok : EncToken) (c : Cfg workTapeCount Q) :
    (controllerScheduledCfg mode tok c).work = c.work := rfl

/--
@isnad1 id=eq.0h4v.s4.f00ab80316fa from=translated src=- shape=1079ce9c vocab=1365addf
-/
@[simp] theorem controllerScheduledCfg_output {Q : Type}
    (mode : StreamMode) (tok : EncToken) (c : Cfg workTapeCount Q) :
    (controllerScheduledCfg mode tok c).output = c.output := rfl

/-! ## The two bit-reading steps -/

/-- Read the first nonblank input bit, advancing right and preserving parked
work and output tapes.
@isnad1 id=eq.3h4v.s5.6767dd5cb3d7 from=translated src=- shape=b06b5da7 vocab=094cbb64
-/
theorem validEmitterTM_read_first_step_internal {Q : Type}
    (mode : StreamMode) (bit : Bool) (c : Cfg workTapeCount Q)
    (hread : c.input.read = Γ.ofBool bit)
    (hwork : ∀ i, TM.Parked (c.work i)) (hout : TM.Parked c.output) :
    validEmitterTM.step (controllerReadCfg mode c) =
      some (controllerSecondCfg mode bit c) := by
  have hworkIdle :
      (fun i => (c.work i).writeAndMove (TM.readBackWrite (c.work i).read)
        (TM.idleDir (c.work i).read)) = c.work := by
    funext i
    exact (hwork i).writeAndMove_readBack_idle
  have houtIdle :
      c.output.writeAndMove (TM.readBackWrite c.output.read)
        (TM.idleDir c.output.read) = c.output :=
    hout.writeAndMove_readBack_idle
  cases bit <;>
    simp [validEmitterTM, TM.step, controllerReadCfg, controllerSecondCfg,
      controllerRead, controllerDone, hread, Γ.ofBool]
  all_goals
    constructor
    · simpa only [Γw.toΓ] using hworkIdle
    · simpa only [Γw.toΓ] using houtIdle

/-- Read the second nonblank input bit, schedule its decoded token, advance
right, and preserve parked work and output tapes.
@isnad1 id=eq.3h5v.s6.1d940b371a46 from=translated src=- shape=ec38a369 vocab=03bf16c7
-/
theorem validEmitterTM_read_second_step_internal {Q : Type}
    (mode : StreamMode) (first second : Bool) (c : Cfg workTapeCount Q)
    (hread : (c.input.move .right).read = Γ.ofBool second)
    (hwork : ∀ i, TM.Parked (c.work i)) (hout : TM.Parked c.output) :
    validEmitterTM.step (controllerSecondCfg mode first c) =
      some (controllerScheduledCfg mode (tokenOfPair first second) c) := by
  have hworkIdle :
      (fun i => (c.work i).writeAndMove (TM.readBackWrite (c.work i).read)
        (TM.idleDir (c.work i).read)) = c.work := by
    funext i
    exact (hwork i).writeAndMove_readBack_idle
  have houtIdle :
      c.output.writeAndMove (TM.readBackWrite c.output.read)
        (TM.idleDir c.output.read) = c.output :=
    hout.writeAndMove_readBack_idle
  cases second <;>
    simp [validEmitterTM, TM.step, controllerSecondCfg, controllerScheduledCfg,
      controllerRead, controllerDone, hread, Γ.ofBool]
  all_goals
    constructor
    · simpa only [Γw.toΓ] using hworkIdle
    · simpa only [Γw.toΓ] using houtIdle

/-- Reading the two concrete bits of `tok` schedules that token in exactly two
controller steps. The endpoint records exact head/cell and tape framing.
@isnad1 id=reachesi.3h4v.s5.46c37397f467 from=translated src=- shape=81f83645 vocab=84862de2
-/
theorem validEmitterTM_read_token_reachesIn_internal {Q : Type}
    (mode : StreamMode) (tok : EncToken) (c : Cfg workTapeCount Q)
    (hinput : InputTokenAt c.input tok)
    (hwork : ∀ i, TM.Parked (c.work i)) (hout : TM.Parked c.output) :
    validEmitterTM.reachesIn 2 (controllerReadCfg mode c)
      (controllerScheduledCfg mode tok c) := by
  have hfirst := validEmitterTM_read_first_step_internal mode
    (tokenFirstBit tok) c hinput.1 hwork hout
  have hsecond := validEmitterTM_read_second_step_internal mode
    (tokenFirstBit tok) (tokenSecondBit tok) c hinput.2 hwork hout
  rw [tokenOfPair_token_bits] at hsecond
  exact .step hfirst (.step hsecond .zero)

/-! ## Trailing blank -/

/-- A blank in first-bit mode halts the controller in one step and preserves
the input and all parked work/output tapes.
@isnad1 id=eq.3h3v.s5.b929bdf413c9 from=translated src=- shape=a177f5ce vocab=378387e5
-/
theorem validEmitterTM_read_blank_step_internal {Q : Type}
    (mode : StreamMode) (c : Cfg workTapeCount Q)
    (hread : c.input.read = Γ.blank)
    (hwork : ∀ i, TM.Parked (c.work i)) (hout : TM.Parked c.output) :
    validEmitterTM.step (controllerReadCfg mode c) =
      some (controllerDoneCfg c) := by
  have hinpIdle : c.input.move (TM.idleDir c.input.read) = c.input := by
    simp [hread, TM.idleDir, Tape.move]
  have hworkIdle :
      (fun i => (c.work i).writeAndMove (TM.readBackWrite (c.work i).read)
        (TM.idleDir (c.work i).read)) = c.work := by
    funext i
    exact (hwork i).writeAndMove_readBack_idle
  have houtIdle :
      c.output.writeAndMove (TM.readBackWrite c.output.read)
        (TM.idleDir c.output.read) = c.output :=
    hout.writeAndMove_readBack_idle
  simp [validEmitterTM, TM.step, controllerReadCfg, controllerDoneCfg,
    controllerRead, controllerDone, hread]
  constructor
  · simpa only [hread] using hinpIdle
  · constructor
    · simpa only [Γw.toΓ] using hworkIdle
    · simpa only [Γw.toΓ] using houtIdle

/-- Exact one-step reachability form of the first-bit blank transition.
@isnad1 id=reachesi.3h3v.s5.805920147807 from=translated src=- shape=c050b5ce vocab=7935b3fe
-/
theorem validEmitterTM_read_blank_reachesIn_internal {Q : Type}
    (mode : StreamMode) (c : Cfg workTapeCount Q)
    (hread : c.input.read = Γ.blank)
    (hwork : ∀ i, TM.Parked (c.work i)) (hout : TM.Parked c.output) :
    validEmitterTM.reachesIn 1 (controllerReadCfg mode c) (controllerDoneCfg c) :=
  .step (validEmitterTM_read_blank_step_internal mode c hread hwork hout) .zero

end Machine

end ThreeSAT

end SAT

end Complexity
