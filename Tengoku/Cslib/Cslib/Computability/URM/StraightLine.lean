/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
module

public import Tengoku.Cslib.Cslib.Computability.URM.Basic
public import Tengoku.Cslib.Cslib.Computability.URM.Execution

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Straight-Line Programs

This file defines straight-line programs (those without jumps) and proves
they always halt exactly at their length.

## Main definitions

- `Program.IsStraightLine`: a program contains no jump instructions

## Main results

- `straight_line_halts`: straight-line programs always halt
- `straightLinefinalState`: final state after running a straight-line program
-/

@[expose] public section

namespace Cslib.URM

/-! ## Straight-Line Programs -/

/-- A program is "straight-line" if it contains no jump instructions.-/
def Program.IsStraightLine (p : Program) : Prop :=
  ∀ i ∈ p, ¬i.IsJump

instance (p : Program) : Decidable p.IsStraightLine :=
  inferInstanceAs (Decidable (∀ i ∈ p, ¬i.IsJump))

/-- Append preserves straight-line property.
@isnad1 id=isstraig.2h2v.s4.e9bcbcfcb993 from=translated src=- shape=255dce7b vocab=7ac89b67
-/
theorem Program.IsStraightLine.append {p q : Program}
    (hp : p.IsStraightLine) (hq : q.IsStraightLine) :
    (p ++ q).IsStraightLine := by
  intro i hi
  simp only [List.mem_append] at hi
  rcases hi with hi | hi <;> [exact hp i hi; exact hq i hi]

/-- Cons of non-jumping instruction preserves straight-line.
@isnad1 id=isstraig.2h2v.s4.df799f79ea6f from=translated src=- shape=5c9e3bb4 vocab=8706e80b
-/
theorem Program.IsStraightLine.cons {instr : Instr} {p : Program}
    (hinstr : ¬instr.IsJump) (hp : p.IsStraightLine) :
    Program.IsStraightLine (instr :: p) := by
  intro i hi
  simp only [List.mem_cons] at hi
  rcases hi with rfl | hi <;> [exact hinstr; exact hp i hi]

/-- Singleton non-jumping instruction is straight-line.
@isnad1 id=isstraig.1h1v.s3.c2e9474fa9ac from=translated src=- shape=dc1c6253 vocab=067e6dbf
-/
theorem Program.IsStraightLine.singleton {instr : Instr}
    (h : ¬instr.IsJump) : Program.IsStraightLine [instr] := by
  intro i hi
  simp only [List.mem_singleton] at hi
  exact hi ▸ h

/-! ## Straight-Line Program Execution -/

/-- A non-jumping instruction produces a step that increments PC by 1.
@isnad1 id=ex.2h2v.s6.f47c541c8b84 from=translated src=- shape=76cb0a89 vocab=ed9db744
-/
theorem Step.of_nonJump {p : Program} {s : State} (hlt : s.pc < p.length)
    (hnonjump : ¬(p[s.pc]'hlt).IsJump) :
    ∃ s', Step p s s' ∧ s'.pc = s.pc + 1 := by
  cases hp : (p[s.pc]'hlt) with
  | Z n =>
    use {pc := s.pc + 1, regs := s.regs.write n 0}
    grind
  | S n =>
    use { pc := s.pc + 1, regs := s.regs.write n (s.regs.read n + 1) }
    grind
  | T m n =>
    use { pc := s.pc + 1, regs := s.regs.write n (s.regs.read m) }
    grind
  | J _ _ _ => grind [Instr.IsJump]

/-- Straight-line programs halt from any starting registers, not just State.init.
Useful for chaining: after running one program, we can run the next
straight-line segment from whatever registers we're in.
@isnad1 id=ex.1h2v.s5.6facd447a1c0 from=translated src=- shape=cffadab6 vocab=368539dc
-/
theorem straight_line_halts_from_regs {p : Program} (hsl : p.IsStraightLine) (r : Regs) :
    ∃ s, Steps p ⟨0, r⟩ s ∧ s.isHalted p ∧ s.pc = p.length := by
  suffices h : ∀ s : State, s.pc ≤ p.length → ∃ s', Steps p s s' ∧ s'.pc = p.length by
    obtain ⟨s', hsteps, hpc'⟩ := h ⟨0, r⟩ (Nat.zero_le _)
    exact ⟨s', hsteps, Nat.le_of_eq hpc'.symm, hpc'⟩
  intro s hpc_le
  generalize hrem : p.length - s.pc = remaining
  induction remaining using Nat.strong_induction_on generalizing s with
  | h n ih =>
  by_cases hhalted : p.length ≤ s.pc
  · grind
  · have jmp : ¬p[s.pc].IsJump := by apply hsl; grind
    have := Step.of_nonJump (by lia) jmp
    grind [Relation.ReflTransGen.head]

/-- A straight-line program halts on any input.
@isnad1 id=halts.1h2v.s3.94b3b15c1cb8 from=translated src=- shape=16780632 vocab=66d3c3a0
-/
theorem straight_line_halts {p : Program} (hsl : p.IsStraightLine) (inputs : List ℕ) :
    Halts p inputs := by
  obtain ⟨s, hsteps, hhalted, _⟩ := straight_line_halts_from_regs hsl (Regs.ofInputs inputs)
  exact ⟨s, hsteps, hhalted⟩

/-- The halting state for a straight-line program starting from registers r.
Wraps Classical.choose to hide it from the API.-/
noncomputable def straightLinefinalState {p : Program}
    (hsl : p.IsStraightLine) (r : Regs) : State :=
  Classical.choose (straight_line_halts_from_regs hsl r)

/-- Specification: the state from straightLinefinalState satisfies Steps, isHalted,
and has pc = p.length.
@isnad1 id=other.1h2v.s5.1a5383868ea0 from=translated src=- shape=0a431a23 vocab=195b40f9
-/
theorem straightLinefinalState_spec {p : Program} (hsl : p.IsStraightLine) (r : Regs) :
    let s := straightLinefinalState hsl r
    Steps p ⟨0, r⟩ s ∧ s.isHalted p ∧ s.pc = p.length :=
  Classical.choose_spec (straight_line_halts_from_regs hsl r)

/-- The final registers after running a straight-line program from given starting registers.-/
noncomputable def straightLineFinalRegs {p : Program} (hsl : p.IsStraightLine) (r : Regs) : Regs :=
  (straightLinefinalState hsl r).regs

/-- For a straight-line program, s.regs equals straightLineFinalRegs if halted from r.
@isnad1 id=eq.3h3v.s5.a352e5581163 from=translated src=- shape=77a5b298 vocab=68beef15
-/
theorem straightLineFinalRegs_eq_of_halted {p : Program} (hsl : p.IsStraightLine)
    (r : Regs) (s : State) (hsteps : Steps p ⟨0, r⟩ s) (hhalted : s.isHalted p) :
    s.regs = straightLineFinalRegs hsl r :=
  Steps.eq_of_halts hsteps hhalted (straightLinefinalState_spec hsl r).1
    (straightLinefinalState_spec hsl r).2.1 ▸ rfl

/-- In a straight-line program, we can characterize the state at any intermediate pc.
This gives us the state after executing instructions 0..pc-1.
@isnad1 id=ex.2h3v.s5.6bbf9ed3bd04 from=translated src=- shape=712e5f0d vocab=bdd6b918
-/
theorem straight_line_state_at_pc {p : Program} (hsl : p.IsStraightLine)
    (r : Regs) (targetPc : ℕ) (htarget : targetPc ≤ p.length) :
    ∃ s, Steps p ⟨0, r⟩ s ∧ s.pc = targetPc := by
  induction targetPc with
  | zero => exact ⟨⟨0, r⟩, Relation.ReflTransGen.refl, rfl⟩
  | succ n ih => grind [Step.of_nonJump, Program.IsStraightLine]

end Cslib.URM

end
