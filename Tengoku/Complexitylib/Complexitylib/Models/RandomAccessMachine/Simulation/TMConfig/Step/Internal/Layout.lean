/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig
public import Tengoku.Complexitylib.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Step.Defs

/-!
# TM-to-RAM step layout -- proof internals
-/

public section

namespace Complexity

namespace RAM

namespace TMConfig

namespace Step

/--
@isnad1 id=lt.0h1v.s3.f7efcd489f27 from=translated src=- shape=a311c14d vocab=585c00b2
-/
theorem symbolCode_lt_internal (symbol : Γ) : symbolCode symbol < 4 := by
  cases symbol <;> decide

/--
@isnad1 id=eq.0h1v.s3.fa62e22b251c from=translated src=- shape=674c64a6 vocab=23b15591
-/
theorem symbolAt_code_internal (symbol : Γ) :
    symbolAt ⟨symbolCode symbol, symbolCode_lt_internal symbol⟩ = symbol := by
  exact symbolDecode_code_internal symbol

/--
@isnad1 id=lt.0h3v.s4.e7fd31a870d2 from=translated src=- shape=9841dd51 vocab=4c3429d2
-/
theorem stateCode_lt_internal (tm : TM n) (state : tm.Q) :
    stateCode tm state < Fintype.card tm.Q :=
  (Fintype.equivFin tm.Q state).isLt

/--
@isnad1 id=eq.0h3v.s4.4af8748623e7 from=translated src=- shape=c59134b2 vocab=71f92a3a
-/
theorem headReg_eq_fieldReg_internal (tape : Fin (n + 2)) :
    headReg tape = fieldReg (headField (bound := bound) tape) := by
  simp [headReg]

/--
@isnad1 id=eq.0h4v.s6.38ebe912caa9 from=translated src=- shape=da524fd9 vocab=9e208893
-/
theorem cellBase_add_eq_fieldReg_internal (tape : Fin (n + 2))
    (position : Fin (bound + 1)) :
    cellBase n bound tape + position.val = fieldReg (cellField tape position) := by
  simp [cellBase]

/--
@isnad1 id=le.0h2v.s3.ecb2c6a0af55 from=translated src=- shape=6c8684e5 vocab=789c119e
-/
theorem zeroReg_ge_internal (n bound : ℕ) :
    registerCount n bound ≤ zeroReg n bound := by
  simp [zeroReg, scratchBase]

/--
@isnad1 id=le.0h2v.s3.7d13a260be87 from=translated src=- shape=6c8684e5 vocab=e05909bf
-/
theorem oneReg_ge_internal (n bound : ℕ) :
    registerCount n bound ≤ oneReg n bound := by
  simp [oneReg, scratchBase]

/--
@isnad1 id=le.0h2v.s3.7e810f30be7b from=translated src=- shape=6c8684e5 vocab=77a5d43b
-/
theorem stateScratchReg_ge_internal (n bound : ℕ) :
    registerCount n bound ≤ stateScratchReg n bound := by
  simp [stateScratchReg, scratchBase]

/--
@isnad1 id=le.0h2v.s3.cc9560d8c99c from=translated src=- shape=6c8684e5 vocab=ea557cfa
-/
theorem addressReg_ge_internal (n bound : ℕ) :
    registerCount n bound ≤ addressReg n bound := by
  simp [addressReg, scratchBase]

/--
@isnad1 id=le.0h2v.s3.54c271fa943f from=translated src=- shape=6c8684e5 vocab=d7c43b22
-/
theorem valueReg_ge_internal (n bound : ℕ) :
    registerCount n bound ≤ valueReg n bound := by
  simp [valueReg, scratchBase]

/--
@isnad1 id=le.0h3v.s4.46152db90fa3 from=translated src=- shape=d0ae267c vocab=955c8347
-/
theorem symbolReg_ge_internal (n bound : ℕ) (tape : Fin (n + 2)) :
    registerCount n bound ≤ symbolReg n bound tape := by
  simp [symbolReg, scratchBase]
  omega

/--
@isnad1 id=and.0h2v.s6.429197d17fa5 from=translated src=- shape=dc74f049 vocab=950697f0
-/
theorem scratch_lt_registerLimit_internal (n bound : ℕ) :
    zeroReg n bound < registerLimit n bound ∧
      oneReg n bound < registerLimit n bound ∧
      stateScratchReg n bound < registerLimit n bound ∧
      addressReg n bound < registerLimit n bound ∧
      valueReg n bound < registerLimit n bound ∧
      ∀ tape, symbolReg n bound tape < registerLimit n bound := by
  constructor
  · simp [zeroReg, scratchBase, registerLimit]
    omega
  constructor
  · simp [oneReg, scratchBase, registerLimit]
    omega
  constructor
  · simp [stateScratchReg, scratchBase, registerLimit]
    omega
  constructor
  · simp [addressReg, scratchBase, registerLimit]
    omega
  constructor
  · simp [valueReg, scratchBase, registerLimit]
    omega
  · intro tape
    simp [symbolReg, scratchBase, registerLimit]
    omega

/--
@isnad1 id=storebou.1h4v.s4.1ea61693310b from=translated src=- shape=9a9db025 vocab=1d8f81e0
-/
theorem encodeRegs_storeBounded_internal (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) (hheads : HeadsBounded cfg bound) :
    StoreBounded tm bound (encodeRegs tm bound cfg) := by
  constructor
  · intro reg hnonzero
    have hreg : reg < registerCount n bound := by
      by_contra hnot
      have hzero := encodeRegs_outside_internal tm bound cfg (Nat.le_of_not_gt hnot)
      exact hnonzero hzero
    exact lt_trans hreg (by
      simp [registerLimit, scratchBase]
      omega)
  · intro reg
    by_cases hreg : reg < registerCount n bound
    · rw [encodeRegs, dite_eq_left hreg]
      let field := (fieldEquiv n bound).symm ⟨reg, hreg⟩
      change fieldValue tm bound cfg field ≤ wordBound tm bound
      rcases field with state | headOrCell
      · exact le_trans (Nat.le_of_lt (stateCode_lt_internal tm cfg.state))
          (le_trans (le_max_left _ _) (le_max_right _ _))
      · rcases headOrCell with tape | cell
        · exact le_trans (hheads tape) (le_trans (Nat.le_succ bound)
            (le_trans (le_max_right _ _) (le_max_right _ _)))
        · rcases cell with ⟨tape, position⟩
          have hcode : symbolCode ((tapeAt cfg tape).cells position.val) ≤ 3 := by
            cases (tapeAt cfg tape).cells position.val <;> decide
          have hthree : 3 ≤ registerLimit n bound := by
            simp [registerLimit, scratchBase, registerCount]
          exact le_trans hcode
            (le_trans hthree (le_max_left _ _))
    · simp [encodeRegs, hreg]

/--
@isnad1 id=represen.1h6v.s5.5d55aa60a01c from=translated src=- shape=0317f85e vocab=5ac15132
-/
theorem loadTapeOps_represents_internal {tm : TM n} {bound : ℕ}
    {cfg : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hrepresents : Represents tm bound cfg store) (tape : Fin (n + 2)) :
    Represents tm bound cfg
      (Structured.Basic.execList (loadTapeOps n bound tape) store) := by
  simp only [loadTapeOps, Structured.Basic.execList, Structured.Basic.exec]
  apply Represents.update_outside_internal
  · apply Represents.update_outside_internal
    · exact hrepresents.update_outside_internal (addressReg_ge_internal n bound)
    · exact addressReg_ge_internal n bound
  · exact symbolReg_ge_internal n bound tape

/--
@isnad1 id=eq.2h6v.s6.167ae6dea1dc from=translated src=- shape=8614e024 vocab=2af8f815
-/
theorem loadTapeOps_symbol_internal {tm : TM n} {bound : ℕ}
    {cfg : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hrepresents : Represents tm bound cfg store)
    (hhead : (tapeAt cfg tape).head ≤ bound) :
    Structured.Basic.execList (loadTapeOps n bound tape) store
        (symbolReg n bound tape) =
      symbolCode ((tapeAt cfg tape).read) := by
  have hheadValue := hrepresents (headField (bound := bound) tape)
  rw [← headReg_eq_fieldReg_internal] at hheadValue
  change store (headReg tape) = (tapeAt cfg tape).head at hheadValue
  let position : Fin (bound + 1) := ⟨(tapeAt cfg tape).head, by omega⟩
  have hcellValue := hrepresents (cellField tape position)
  rw [← cellBase_add_eq_fieldReg_internal] at hcellValue
  change store (cellBase n bound tape + position.val) =
    symbolCode ((tapeAt cfg tape).cells position.val) at hcellValue
  have haddressHead : addressReg n bound ≠ headReg tape := by
    intro heq
    have hfield := fieldReg_lt_internal
      (headField (bound := bound) tape)
    rw [← headReg_eq_fieldReg_internal] at hfield
    have hscratch := addressReg_ge_internal n bound
    omega
  have haddressCell :
      addressReg n bound ≠ cellBase n bound tape + position.val := by
    rw [cellBase_add_eq_fieldReg_internal]
    exact ne_of_gt (lt_of_lt_of_le (fieldReg_lt_internal _) (addressReg_ge_internal n bound))
  let first :=
    (Structured.Basic.imm (addressReg n bound) (cellBase n bound tape)).exec store
  let addressed :=
    (Structured.Basic.add (addressReg n bound) (addressReg n bound)
      (headReg tape)).exec first
  have hfirstHead : first (headReg tape) = store (headReg tape) := by
    simp [first, Structured.Basic.exec, Function.update_of_ne (Ne.symm haddressHead)]
  have hfirstAddress : first (addressReg n bound) = cellBase n bound tape := by
    simp [first, Structured.Basic.exec]
  have haddressedAddress :
      addressed (addressReg n bound) =
        cellBase n bound tape + (tapeAt cfg tape).head := by
    simp only [addressed, Structured.Basic.exec, Function.update_self]
    rw [hfirstAddress, hfirstHead, hheadValue]
  have haddressedCell :
      addressed (cellBase n bound tape + position.val) =
        store (cellBase n bound tape + position.val) := by
    simp [addressed, first, Structured.Basic.exec,
      Function.update_of_ne (Ne.symm haddressCell)]
  change ((Structured.Basic.load (symbolReg n bound tape) (addressReg n bound)).exec
      addressed) (symbolReg n bound tape) = _
  simp only [Structured.Basic.exec, Function.update_self]
  rw [haddressedAddress]
  change addressed (cellBase n bound tape + position.val) = _
  rw [haddressedCell, hcellValue]
  rfl

end Step

end TMConfig

end RAM

end Complexity
