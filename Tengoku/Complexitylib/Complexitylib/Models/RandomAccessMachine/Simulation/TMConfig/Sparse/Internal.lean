/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.Defs
public import Tengoku.Complexitylib.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Internal

/-!
# Sparse unbounded TM configuration encoding -- proof internals
-/

public section

namespace Complexity

namespace RAM

namespace TMConfig

namespace Sparse

/--
@isnad1 id=and.0h1v.s5.a0db20c3f078 from=translated src=- shape=c421cc6e vocab=9c5f6afd
-/
theorem control_lt_cellBase_internal (n : ℕ) :
    valueReg n < cellBase n ∧ ∀ tape, symbolReg n tape < cellBase n := by
  constructor
  · simp [valueReg, cellBase]
    omega
  · intro tape
    simp [symbolReg, cellBase]
    omega

/--
@isnad1 id=lt.0h2v.s5.8336e2bc7475 from=translated src=- shape=d84ee594 vocab=0c83a12f
-/
theorem headReg_lt_control_internal (tape : Fin (n + 2)) :
    headReg tape < n + 3 := by
  simp [headReg]
  omega

/--
@isnad1 id=le.0h3v.s4.8ded6401e4b1 from=translated src=- shape=6a1a25ee vocab=f9721f12
-/
theorem cellBase_le_cellReg_internal (tape : Fin (n + 2)) (position : ℕ) :
    cellBase n ≤ cellReg n tape position := by
  simp [cellReg]
  omega

private theorem headPrefix_lt_cellBase (n : ℕ) : n + 3 < cellBase n := by
  simp [cellBase]
  omega

/--
@isnad1 id=eq.0h3v.s5.e87fa629333f from=translated src=- shape=9d6d6bc3 vocab=ce856d3c
-/
theorem decodeCellTape_cellReg_internal (tape : Fin (n + 2)) (position : ℕ) :
    decodeCellTape n (cellReg n tape position) = tape := by
  have hoffset : cellReg n tape position - cellBase n =
      position * (n + 2) + tape.val := by
    simp [cellReg]
    omega
  apply Fin.ext
  change (cellReg n tape position - cellBase n) % (n + 2) = tape.val
  rw [hoffset]
  simp [Nat.add_mod, Nat.mod_eq_of_lt tape.isLt]

/--
@isnad1 id=eq.0h3v.s4.70af796515c8 from=translated src=- shape=1dafcab5 vocab=02361c5f
-/
theorem decodeCellPosition_cellReg_internal (tape : Fin (n + 2))
    (position : ℕ) :
    decodeCellPosition n (cellReg n tape position) = position := by
  have hoffset : cellReg n tape position - cellBase n =
      position * (n + 2) + tape.val := by
    simp [cellReg]
    omega
  rw [decodeCellPosition, hoffset, Nat.add_comm,
    Nat.add_mul_div_right tape.val position (by omega),
    Nat.div_eq_of_lt tape.isLt, Nat.zero_add]

/--
@isnad1 id=injectiv.0h1v.s6.714360c337f3 from=translated src=- shape=be0c4dc8 vocab=acbf208b
-/
theorem cellReg_injective_internal :
    Function.Injective (fun field : Fin (n + 2) × ℕ =>
      cellReg n field.1 field.2) := by
  intro first second heq
  have htape := congrArg (decodeCellTape n) heq
  have hposition := congrArg (decodeCellPosition n) heq
  rw [decodeCellTape_cellReg_internal, decodeCellTape_cellReg_internal] at htape
  rw [decodeCellPosition_cellReg_internal,
    decodeCellPosition_cellReg_internal] at hposition
  exact Prod.ext htape hposition

/--
@isnad1 id=injectiv.0h1v.s3.32cce1cceb51 from=translated src=- shape=9ef37d6b vocab=488308a5
-/
theorem fieldReg_injective_internal : Function.Injective (@fieldReg n) := by
  intro first second heq
  rcases first with state | headOrCell
  · rcases state with ⟨state, hstate⟩
    have hzero : state = 0 := by omega
    subst state
    rcases second with state' | headOrCell'
    · rcases state' with ⟨state', hstate'⟩
      have hzero' : state' = 0 := by omega
      subst state'
      rfl
    · rcases headOrCell' with tape | cell
      · simp [fieldReg, stateReg, headReg] at heq
        omega
      · rcases cell with ⟨tape, position⟩
        have hbase := cellBase_le_cellReg_internal tape position
        simp [fieldReg, stateReg, cellBase] at heq hbase
        omega
  · rcases headOrCell with tape | cell
    · rcases second with state' | headOrCell'
      · rcases state' with ⟨state', hstate'⟩
        have hzero : state' = 0 := by omega
        subst state'
        simp [fieldReg, stateReg, headReg] at heq
      · rcases headOrCell' with tape' | cell'
        · apply congrArg Sum.inr
          apply congrArg Sum.inl
          apply Fin.ext
          simp [fieldReg, headReg] at heq
          omega
        · rcases cell' with ⟨tape', position'⟩
          have hhead := headReg_lt_control_internal tape
          have hcell := cellBase_le_cellReg_internal tape' position'
          have hcontrol := headPrefix_lt_cellBase n
          simp [fieldReg] at heq
          omega
    · rcases cell with ⟨tape, position⟩
      rcases second with state' | headOrCell'
      · rcases state' with ⟨state', hstate'⟩
        have hzero : state' = 0 := by omega
        subst state'
        have hcell := cellBase_le_cellReg_internal tape position
        simp [fieldReg, stateReg, cellBase] at heq hcell
        omega
      · rcases headOrCell' with tape' | cell'
        · have hhead := headReg_lt_control_internal tape'
          have hcell := cellBase_le_cellReg_internal tape position
          simp [fieldReg, cellBase] at heq hcell
          omega
        · rcases cell' with ⟨tape', position'⟩
          have hpairs : (tape, position) = (tape', position') :=
            cellReg_injective_internal heq
          exact congrArg (fun pair => Sum.inr (Sum.inr pair)) hpairs

/--
@isnad1 id=ne.2h3v.s5.5ac094a35677 from=translated src=- shape=ccde8a13 vocab=177f5bf5
-/
theorem fieldReg_ne_control_internal (field : Field n) {reg : ℕ}
    (hlow : n + 3 ≤ reg) (hhigh : reg < cellBase n) :
    fieldReg field ≠ reg := by
  intro heq
  rcases field with state | headOrCell
  · rcases state with ⟨state, hstate⟩
    have hzero : state = 0 := by omega
    subst state
    simp [fieldReg, stateReg] at heq
    omega
  · rcases headOrCell with tape | cell
    · have hhead := headReg_lt_control_internal tape
      simp [fieldReg] at heq
      omega
    · have hcell := cellBase_le_cellReg_internal cell.1 cell.2
      simp [fieldReg] at heq
      omega

/--
@isnad1 id=represen.3h6v.s5.f283ac18bf10 from=translated src=- shape=61015497 vocab=30cff769
-/
theorem Represents.update_control_internal {tm : TM n}
    {cfg : Complexity.Cfg n tm.Q} {store : Structured.Store} {reg value : ℕ}
    (hrepresents : Represents tm cfg store)
    (hlow : n + 3 ≤ reg) (hhigh : reg < cellBase n) :
    Represents tm cfg (Function.update store reg value) := by
  intro field
  rw [Function.update_of_ne (fieldReg_ne_control_internal field hlow hhigh)]
  exact hrepresents field

/--
@isnad1 id=and.0h1v.s7.eff7d161a169 from=translated src=- shape=079c21ce vocab=b9d95f5d
-/
theorem scratch_range_internal (n : ℕ) :
    (n + 3 ≤ zeroReg n ∧ zeroReg n < cellBase n) ∧
    (n + 3 ≤ oneReg n ∧ oneReg n < cellBase n) ∧
    (n + 3 ≤ tapeCountReg n ∧ tapeCountReg n < cellBase n) ∧
    (n + 3 ≤ stateScratchReg n ∧ stateScratchReg n < cellBase n) ∧
    (n + 3 ≤ addressReg n ∧ addressReg n < cellBase n) ∧
    (n + 3 ≤ valueReg n ∧ valueReg n < cellBase n) ∧
    ∀ tape, n + 3 ≤ symbolReg n tape ∧ symbolReg n tape < cellBase n := by
  constructor
  · simp [zeroReg, cellBase]
    omega
  constructor
  · simp [oneReg, cellBase]
    omega
  constructor
  · simp [tapeCountReg, cellBase]
    omega
  constructor
  · simp [stateScratchReg, cellBase]
    omega
  constructor
  · simp [addressReg, cellBase]
    omega
  constructor
  · simp [valueReg, cellBase]
    omega
  · intro tape
    have htape := tape.isLt
    simp [symbolReg, cellBase]
    omega

/--
@isnad1 id=eq.0h3v.s4.8cbfaf3af4ff from=translated src=- shape=b24cce09 vocab=b4143e2e
-/
theorem encodeRegs_state_internal (tm : TM n) (cfg : Complexity.Cfg n tm.Q) :
    encodeRegs tm cfg stateReg = stateCode tm cfg.state := by
  simp [encodeRegs, stateReg]

/--
@isnad1 id=eq.0h4v.s5.854bef73423f from=translated src=- shape=e9f422f4 vocab=181af6ad
-/
theorem encodeRegs_head_internal (tm : TM n) (cfg : Complexity.Cfg n tm.Q)
    (tape : Fin (n + 2)) :
    encodeRegs tm cfg (headReg tape) = (tapeAt cfg tape).head := by
  have hstate : headReg tape ≠ stateReg := by
    simp [headReg, stateReg]
  rw [encodeRegs, dite_eq_right hstate,
    dite_eq_left (headReg_lt_control_internal tape)]
  congr 2
  apply Fin.ext
  simp [headReg]

/--
@isnad1 id=eq.0h5v.s5.8b7ffb150d9b from=translated src=- shape=78a224f0 vocab=bcb03cdb
-/
theorem encodeRegs_cell_internal (tm : TM n) (cfg : Complexity.Cfg n tm.Q)
    (tape : Fin (n + 2)) (position : ℕ) :
    encodeRegs tm cfg (cellReg n tape position) =
      symbolCode ((tapeAt cfg tape).cells position) := by
  have hbase := cellBase_le_cellReg_internal tape position
  have hcontrol := headPrefix_lt_cellBase n
  have hnotState : cellReg n tape position ≠ stateReg := by
    simp [stateReg]
    omega
  have hnotHead : ¬ cellReg n tape position < n + 3 := by omega
  rw [encodeRegs, dite_eq_right hnotState, dite_eq_right hnotHead, ite_eq_left hbase,
    decodeCellTape_cellReg_internal, decodeCellPosition_cellReg_internal]

/--
@isnad1 id=represen.0h3v.s4.483e081d406d from=translated src=- shape=176c88a0 vocab=a5738c80
-/
theorem encodeRegs_represents_internal (tm : TM n)
    (cfg : Complexity.Cfg n tm.Q) : Represents tm cfg (encodeRegs tm cfg) := by
  intro field
  rcases field with state | headOrCell
  · rcases state with ⟨state, hstate⟩
    have hzero : state = 0 := by omega
    subst state
    exact encodeRegs_state_internal tm cfg
  · rcases headOrCell with tape | cell
    · exact encodeRegs_head_internal tm cfg tape
    · exact encodeRegs_cell_internal tm cfg cell.1 cell.2

/--
@isnad1 id=eq.1h4v.s4.aeed8c33efae from=translated src=- shape=722246ec vocab=b2947fe7
-/
theorem decode_of_represents_internal (tm : TM n)
    (cfg : Complexity.Cfg n tm.Q) (store : Structured.Store)
    (hrepresents : Represents tm cfg store) : decode tm store = cfg := by
  apply Complexity.Cfg.ext
  · simp only [decode]
    have hstate := hrepresents (Sum.inl ⟨0, by omega⟩)
    change store stateReg = stateCode tm cfg.state at hstate
    rw [hstate]
    exact stateDecode_code_internal tm cfg.state
  · apply Tape.ext
    · simpa [decode, decodeTape, tapeAt, fieldReg, fieldValue] using
        hrepresents (Sum.inr (Sum.inl ⟨0, by omega⟩))
    · funext position
      simp only [decode, decodeTape]
      have hcell := hrepresents
        (Sum.inr (Sum.inr (⟨0, by omega⟩, position)))
      change store (cellReg n ⟨0, by omega⟩ position) =
        symbolCode ((tapeAt cfg ⟨0, by omega⟩).cells position) at hcell
      rw [hcell, symbolDecode_code_internal, tapeAt_input_internal]
  · funext i
    apply Tape.ext
    · have hhead := hrepresents (Sum.inr (Sum.inl ⟨i.val + 1, by omega⟩))
      change store (headReg ⟨i.val + 1, by omega⟩) =
        (tapeAt cfg ⟨i.val + 1, by omega⟩).head at hhead
      simpa [decode, decodeTape, tapeAt_work_internal] using hhead
    · funext position
      simp only [decode, decodeTape]
      have hcell := hrepresents
        (Sum.inr (Sum.inr (⟨i.val + 1, by omega⟩, position)))
      change store (cellReg n ⟨i.val + 1, by omega⟩ position) =
        symbolCode ((tapeAt cfg ⟨i.val + 1, by omega⟩).cells position) at hcell
      rw [hcell, symbolDecode_code_internal, tapeAt_work_internal]
  · apply Tape.ext
    · have hhead := hrepresents (Sum.inr (Sum.inl ⟨n + 1, by omega⟩))
      change store (headReg ⟨n + 1, by omega⟩) =
        (tapeAt cfg ⟨n + 1, by omega⟩).head at hhead
      simpa [decode, decodeTape, tapeAt_output_internal] using hhead
    · funext position
      simp only [decode, decodeTape]
      have hcell := hrepresents
        (Sum.inr (Sum.inr (⟨n + 1, by omega⟩, position)))
      change store (cellReg n ⟨n + 1, by omega⟩ position) =
        symbolCode ((tapeAt cfg ⟨n + 1, by omega⟩).cells position) at hcell
      rw [hcell, symbolDecode_code_internal, tapeAt_output_internal]

/--
@isnad1 id=eq.0h3v.s4.a20c141229b9 from=translated src=- shape=09807c37 vocab=50ca22c3
-/
theorem decode_encode_internal (tm : TM n) (cfg : Complexity.Cfg n tm.Q) :
    decode tm (encodeRegs tm cfg) = cfg :=
  decode_of_represents_internal tm cfg (encodeRegs tm cfg)
    (encodeRegs_represents_internal tm cfg)

end Sparse

end TMConfig

end RAM

end Complexity
