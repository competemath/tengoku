/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Defs

/-!
# Bounded Turing-machine configuration encoding -- proof internals
-/

public section

namespace Complexity

namespace RAM

namespace TMConfig

/--
@isnad1 id=eq.0h2v.s4.3559e0a59bb8 from=translated src=- shape=515d1a8c vocab=27edd30b
-/
theorem fieldReg_state_internal :
    fieldReg (stateField (n := n) (bound := bound)) = 0 := by
  rfl

/--
@isnad1 id=eq.0h3v.s5.1961c2cbd9c1 from=translated src=- shape=3b4ccabb vocab=fbf7afbe
-/
theorem fieldReg_head_internal (tape : Fin (n + 2)) :
    fieldReg (headField (bound := bound) tape) = 1 + tape.val := by
  rfl

/--
@isnad1 id=eq.0h4v.s7.5e7d93f370ee from=translated src=- shape=21a84a7e vocab=12f331b1
-/
theorem fieldReg_cell_internal (tape : Fin (n + 2))
    (position : Fin (bound + 1)) :
    fieldReg (cellField tape position) =
      1 + (n + 2) + tape.val * (bound + 1) + position.val := by
  simp [fieldReg, cellField, fieldEquiv, finProdFinEquiv, Nat.mul_comm]
  simp [finSumFinEquiv]
  change 1 + (n + 2 + (position.val + tape.val * (bound + 1))) = _
  omega

/--
@isnad1 id=eq.0h1v.s3.13fe149fa7a9 from=translated src=- shape=47dcad53 vocab=e5b95926
-/
theorem symbolDecode_code_internal (symbol : Γ) :
    symbolDecode (symbolCode symbol) = symbol := by
  cases symbol <;> rfl

/--
@isnad1 id=eq.0h3v.s4.e9f2617f4deb from=translated src=- shape=9a6007cb vocab=aecfe2bd
-/
theorem stateDecode_code_internal (tm : TM n) (state : tm.Q) :
    stateDecode tm (stateCode tm state) = state := by
  simp [stateDecode, stateCode]

/--
@isnad1 id=eq.0h3v.s5.7e441f7d709a from=translated src=- shape=611f5328 vocab=2c0c992f
-/
theorem tapeAt_input_internal (cfg : Complexity.Cfg n Q) :
    tapeAt cfg ⟨0, by omega⟩ = cfg.input := by
  simp [tapeAt]

/--
@isnad1 id=eq.0h4v.s5.80356873d52b from=translated src=- shape=d0b386c4 vocab=2eb3f744
-/
theorem tapeAt_work_internal (cfg : Complexity.Cfg n Q) (i : Fin n) :
    tapeAt cfg ⟨i.val + 1, by omega⟩ = cfg.work i := by
  simp only [tapeAt]
  rw [dite_eq_right (by omega), dite_eq_right (by omega)]
  congr 1

/--
@isnad1 id=eq.0h3v.s5.f9c5abcd4eb2 from=translated src=- shape=e0446d7e vocab=0d883b97
-/
theorem tapeAt_output_internal (cfg : Complexity.Cfg n Q) :
    tapeAt cfg ⟨n + 1, by omega⟩ = cfg.output := by
  simp [tapeAt]

/--
@isnad1 id=eq.0h5v.s5.4938dc719b6b from=translated src=- shape=7d3b08de vocab=b71c4d7b
-/
theorem encodeRegs_field_internal (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) (field : Field n bound) :
    encodeRegs tm bound cfg (fieldReg field) = fieldValue tm bound cfg field := by
  have hreg : fieldReg field < registerCount n bound :=
    (fieldEquiv n bound field).isLt
  unfold encodeRegs
  rw [dite_eq_left hreg]
  have hfield :
      (⟨fieldReg field, hreg⟩ : Fin (registerCount n bound)) =
        fieldEquiv n bound field := by
    apply Fin.ext
    rfl
  rw [hfield, Equiv.symm_apply_apply]

/--
@isnad1 id=lt.0h3v.s4.3d086c044334 from=translated src=- shape=cdc6fac2 vocab=8e04350a
-/
theorem fieldReg_lt_internal (field : Field n bound) :
    fieldReg field < registerCount n bound :=
  (fieldEquiv n bound field).isLt

/--
@isnad1 id=injectiv.0h2v.s3.e45da644d67e from=translated src=- shape=a3f091f9 vocab=bc8650dd
-/
theorem fieldReg_injective_internal :
    Function.Injective (@fieldReg n bound) := by
  intro first second heq
  apply (fieldEquiv n bound).injective
  exact Fin.ext heq

/--
@isnad1 id=represen.2h7v.s5.33e7cd75838a from=translated src=- shape=29660fff vocab=5eed5e73
-/
theorem Represents.update_outside_internal {tm : TM n} {bound reg value : ℕ}
    {cfg : Complexity.Cfg n tm.Q} {regs : ℕ → ℕ}
    (hrepresents : Represents tm bound cfg regs)
    (hreg : registerCount n bound ≤ reg) :
    Represents tm bound cfg (Function.update regs reg value) := by
  intro field
  rw [Function.update_of_ne]
  · exact hrepresents field
  · exact fun heq => (not_lt_of_ge hreg) (heq ▸ fieldReg_lt_internal field)

/--
@isnad1 id=represen.0h4v.s4.029831086e1a from=translated src=- shape=e1b49d5e vocab=93c7d2db
-/
theorem encodeRegs_represents_internal (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) :
    Represents tm bound cfg (encodeRegs tm bound cfg) :=
  encodeRegs_field_internal tm bound cfg

private theorem decodeTape_of_represents (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) (regs : ℕ → ℕ)
    (hrepresents : Represents tm bound cfg regs)
    (hbounded : Bounded cfg bound) (tape : Fin (n + 2)) :
    decodeTape bound regs tape = tapeAt cfg tape := by
  apply Tape.ext
  · simp only [decodeTape]
    rw [hrepresents (headField (bound := bound) tape)]
    rfl
  · funext position
    by_cases hposition : position < bound + 1
    · simp only [decodeTape, hposition, dite_eq_left]
      rw [hrepresents (cellField tape ⟨position, hposition⟩)]
      exact symbolDecode_code_internal _
    · simp only [decodeTape, hposition]
      exact (hbounded tape position (by omega)).symm

/--
@isnad1 id=eq.2h5v.s5.436d60d2593b from=translated src=- shape=94c425ba vocab=3e0d3de4
-/
theorem decode_of_represents_internal (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) (regs : ℕ → ℕ)
    (hrepresents : Represents tm bound cfg regs)
    (hbounded : Bounded cfg bound) : decode tm bound regs = cfg := by
  apply Complexity.Cfg.ext
  · simp only [decode]
    rw [hrepresents (stateField (n := n) (bound := bound))]
    exact stateDecode_code_internal tm cfg.state
  · rw [← tapeAt_input_internal cfg]
    simpa [decode] using
      decodeTape_of_represents tm bound cfg regs hrepresents hbounded
        ⟨0, by omega⟩
  · funext i
    simpa [decode, tapeAt_work_internal] using
      decodeTape_of_represents tm bound cfg regs hrepresents hbounded
        ⟨i.val + 1, by omega⟩
  · simpa [decode, tapeAt_output_internal] using
      decodeTape_of_represents tm bound cfg regs hrepresents hbounded
        ⟨n + 1, by omega⟩

/--
@isnad1 id=eq.1h4v.s5.39f386e2b7ac from=translated src=- shape=4f6e2a7a vocab=63652974
-/
theorem decode_encode_internal (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) (hbounded : Bounded cfg bound) :
    decode tm bound (encode tm bound cfg).regs = cfg := by
  exact decode_of_represents_internal tm bound cfg (encode tm bound cfg).regs
    (encodeRegs_represents_internal tm bound cfg) hbounded

/--
@isnad1 id=eq.1h5v.s5.86c19ada1f74 from=translated src=- shape=3e639e0e vocab=5aac81bc
-/
theorem encodeRegs_outside_internal (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) {reg : ℕ}
    (hreg : registerCount n bound ≤ reg) :
    encodeRegs tm bound cfg reg = 0 := by
  simp [encodeRegs, Nat.not_lt.mpr hreg]

end TMConfig

end RAM

end Complexity
