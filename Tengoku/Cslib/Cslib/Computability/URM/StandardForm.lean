/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
module

public import Tengoku.Cslib.Cslib.Computability.URM.StraightLine

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Standard Form Programs

This file defines standard-form programs (those with bounded jump targets)
and proves their execution properties.

## Main definitions

- `Program.IsStandardForm`: all jump targets are bounded by program length
- `Program.toStandardForm`: convert a program to standard form

## Main results

- `straight_line_IsStandardForm`: straight-line programs are standard form
- `Halts.toStandardForm_iff`: halting equivalence with normalized programs
-/

@[expose] public section

namespace Cslib.URM

/-! ## Standard Form Definitions -/

namespace Program

/-- A program is in standard form if all jump targets are bounded by the program length.
Jumps can target any instruction (0..length-1) or the "virtual halt" position (length).-/
def IsStandardForm (p : Program) : Prop :=
  ∀ instr ∈ p, instr.JumpsBoundedBy p.length

instance (p : Program) : Decidable p.IsStandardForm :=
  inferInstanceAs (Decidable (∀ instr ∈ p, instr.JumpsBoundedBy p.length))

/-- Convert a program to standard form by capping all jump targets at the program length.-/
def toStandardForm (p : Program) : Program :=
  p.map (Instr.capJump p.length)

/-- toStandardForm preserves program length.
@isnad1 id=eq.0h1v.s3.aca5a4730862 from=translated src=- shape=62661159 vocab=5bad653d
-/
@[simp, scoped grind =]
theorem toStandardForm_length (p : Program) : p.toStandardForm.length = p.length := by
  simp [toStandardForm]

/-- toStandardForm produces a standard form program.
@isnad1 id=isstanda.0h1v.s2.65b90983116d from=translated src=- shape=76a08d12 vocab=f94e0030
-/
theorem toStandardForm_isStandardForm (p : Program) :
    p.toStandardForm.IsStandardForm := by
  unfold IsStandardForm toStandardForm
  rw [List.length_map]
  intro instr hinstr
  obtain ⟨orig, _, rfl⟩ := List.mem_map.mp hinstr
  exact Instr.JumpsBoundedBy.capJump p.length orig

/-- Accessing an instruction in toStandardForm gives the capJump'd instruction.
@isnad1 id=eq.0h2v.s5.2b1f17321953 from=translated src=- shape=cfe03f05 vocab=7e7ea586
-/
theorem getElem?_toStandardForm (p : Program) (i : ℕ) :
    p.toStandardForm[i]? = (p[i]?).map (Instr.capJump p.length) := by
  simp only [toStandardForm, List.getElem?_map]

/-- toStandardForm is idempotent: applying it twice equals applying it once.
@isnad1 id=eq.0h1v.s3.03c31a06c062 from=translated src=- shape=9bfe7af5 vocab=0ede2311
-/
@[simp]
theorem toStandardForm_idempotent (p : Program) :
    p.toStandardForm.toStandardForm = p.toStandardForm := by
  simp only [toStandardForm, List.length_map, List.map_map]
  congr 1
  funext instr
  exact Instr.capJump_idempotent p.length instr

end Program

/-! ## Standard Form Properties -/

/-- Straight-line programs are in standard form.
@isnad1 id=isstanda.1h1v.s2.e0216b2a3af4 from=translated src=- shape=6321fd23 vocab=63a0088b
-/
theorem straight_line_IsStandardForm {p : Program} (hsl : p.IsStraightLine) :
    p.IsStandardForm := by
  intro instr hinstr
  exact Instr.jumpsBoundedBy_of_nonJump (hsl instr hinstr) p.length

/-! ## Bisimulation

`p` and `p.toStandardForm` are bisimilar: each step in one program corresponds to a
step in the other that either reaches the same state or reaches a halted state with the
same registers. This bisimulation implies functional equivalence (`eval_toStandardForm`).
The key insight is that jumps with target `q > p.length` land in halted states in both
programs. -/

/-- Forward step correspondence: if p steps from s to s', then either:
    (1) p.toStandardForm steps from s to s' (same step), or
    (2) s' is halted in p, and p.toStandardForm steps to a state that is also halted
        with the same registers (this only happens for jumps with unbounded targets).
@isnad1 id=or.1h3v.s5.8136cbb1575e from=translated src=- shape=a18b56c0 vocab=6a3c04f2
-/
theorem Step.toStandardForm {p : Program} {s s' : State} (hstep : Step p s s') :
    Step p.toStandardForm s s' ∨
    (s'.isHalted p ∧ ∃ s₂, Step p.toStandardForm s s₂ ∧
      s₂.isHalted p.toStandardForm ∧ s'.regs = s₂.regs) := by
  cases hstep with
  | zero hinstr =>
    left
    exact Step.zero (by simp [Program.getElem?_toStandardForm, hinstr])
  | succ hinstr =>
    left
    exact Step.succ (by simp [Program.getElem?_toStandardForm, hinstr])
  | transfer hinstr =>
    left
    exact Step.transfer (by simp [Program.getElem?_toStandardForm, hinstr])
  | @jump_ne m n q hinstr hne =>
    left
    have hcap : p.toStandardForm[s.pc]? = some (Instr.J m n (min q p.length)) := by
      simp [Program.getElem?_toStandardForm, hinstr]
    exact Step.jump_ne hcap hne
  | @jump_eq m n q hinstr heq =>
    have (x : ℕ) (h : min q p.length = x) : p.toStandardForm[s.pc]? = some (Instr.J m n x) := by
      grind [Program.getElem?_toStandardForm, Instr.capJump]
    by_cases q ≤ p.length
    · grind [Step.jump_eq]
    · right
      split_ands
      · grind [State.isHalted]
      · use ⟨p.length, s.regs⟩
        grind [State.isHalted, Program.toStandardForm_length]

/-- Forward halting: if p reaches a halted state, p.toStandardForm reaches a halted state
    with the same registers.
@isnad1 id=ex.2h3v.s5.41274b887d43 from=translated src=- shape=02697728 vocab=37bad991
-/
theorem Steps.toStandardForm_halts {p : Program} {s s' : State}
    (hsteps : Steps p s s') (hhalted : s'.isHalted p) :
    ∃ s₂, Steps p.toStandardForm s s₂ ∧
      s₂.isHalted p.toStandardForm ∧ s'.regs = s₂.regs := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl =>
    refine ⟨s', .refl, ?_, rfl⟩
    simp only [State.isHalted, Program.toStandardForm_length]
    exact hhalted
  | head hstep hrest ih =>
    rcases Step.toStandardForm hstep with
      hsame | ⟨hhalted_mid, s_mid, hstep_mid, hhalted_mid', hregs_eq⟩
    · obtain ⟨s₂, hsteps₂, hhalted₂, hregs_eq⟩ := ih
      exact ⟨s₂, .head hsame hsteps₂, hhalted₂, hregs_eq⟩
    · grind [Steps.eq_of_halts .refl hhalted_mid hrest hhalted]

/-- Forward halting theorem.
@isnad1 id=halts.1h2v.s3.76dd3ca2246f from=translated src=- shape=3391551a vocab=b025220d
-/
theorem Halts.toStandardForm {p : Program} {inputs : List ℕ} (h : Halts p inputs) :
    Halts p.toStandardForm inputs := by
  obtain ⟨s, hsteps, hhalted⟩ := h
  obtain ⟨s₂, hsteps₂, hhalted₂, _⟩ := Steps.toStandardForm_halts hsteps hhalted
  exact ⟨s₂, hsteps₂, hhalted₂⟩

open Program State Instr in
/-- Reverse step correspondence: if p.toStandardForm steps from s to s', then either:
    (1) p steps from s to s' (same step), or
    (2) s' is halted in p.toStandardForm, and p steps to a state that is also halted
        with the same registers (this only happens for jumps with unbounded targets).
@isnad1 id=or.1h3v.s5.d24be58aa814 from=translated src=- shape=73381abf vocab=6a3c04f2
-/
theorem Step.from_toStandardForm {p : Program} {s s' : State} (hstep : Step p.toStandardForm s s') :
    Step p s s' ∨
    (s'.isHalted p.toStandardForm ∧ ∃ s₂, Step p s s₂ ∧ s₂.isHalted p ∧ s'.regs = s₂.regs) := by
  cases hstep with
  | jump_eq hinstr _ =>
    simp only [Program.getElem?_toStandardForm, Option.map_eq_some_iff] at hinstr
    obtain ⟨instr, _⟩ := hinstr
    cases instr with
    | J => grind [=> jump_eq]
    | _ => grind
  | _ => grind [getElem?_toStandardForm, Option.map_eq_some_iff]

/-- Reverse halting: if p.toStandardForm reaches a halted state, p reaches a halted state
    with the same registers.
@isnad1 id=ex.2h3v.s5.ede9342c6adb from=translated src=- shape=2970fb20 vocab=37bad991
-/
theorem Steps.from_toStandardForm_halts {p : Program} {s s' : State}
    (hsteps : Steps p.toStandardForm s s') (hhalted : s'.isHalted p.toStandardForm) :
    ∃ s₂, Steps p s s₂ ∧ s₂.isHalted p ∧ s'.regs = s₂.regs := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl =>
    refine ⟨s', by rfl, ?_, rfl⟩
    simp only [State.isHalted, Program.toStandardForm_length] at hhalted ⊢
    exact hhalted
  | head hstep hrest ih =>
    rcases Step.from_toStandardForm hstep with
      hsame | ⟨hhalted_mid, s_mid, hstep_mid, hhalted_mid', hregs_eq⟩
    · obtain ⟨s₂, hsteps₂, hhalted₂, hregs_eq⟩ := ih
      exact ⟨s₂, .head hsame hsteps₂, hhalted₂, hregs_eq⟩
    · rename_i s_next
      have hrest_trivial : s_next = s' := Steps.eq_of_halts .refl hhalted_mid hrest hhalted
      subst hrest_trivial
      exact ⟨s_mid, .single hstep_mid, hhalted_mid', hregs_eq⟩

/-- Reverse halting theorem.
@isnad1 id=halts.1h2v.s3.e69e14445066 from=translated src=- shape=a0fbf760 vocab=b025220d
-/
theorem Halts.of_toStandardForm {p : Program} {inputs : List ℕ}
    (h : Halts p.toStandardForm inputs) : Halts p inputs := by
  obtain ⟨s, hsteps, hhalted⟩ := h
  obtain ⟨s₂, hsteps₂, hhalted₂, _⟩ := Steps.from_toStandardForm_halts hsteps hhalted
  exact ⟨s₂, hsteps₂, hhalted₂⟩

/-- Halting equivalence: original halts iff standard form halts.
@isnad1 id=iff.0h2v.s3.0c608584b034 from=translated src=- shape=6d80e643 vocab=b025220d
-/
theorem Halts.toStandardForm_iff {p : Program} {inputs : List ℕ} :
    Halts p inputs ↔ Halts p.toStandardForm inputs :=
  ⟨Halts.toStandardForm, Halts.of_toStandardForm⟩

/-! ### eval Preservation -/

/-- Registers preservation: both reach states with the same registers.
@isnad1 id=eq.2h2v.s5.07eacb03f313 from=translated src=- shape=d50e59e6 vocab=96de603f
-/
theorem evalState_toStandardForm_regs {p : Program} {inputs : List ℕ}
    (hp : (evalState p inputs).Dom) (hq : (evalState p.toStandardForm inputs).Dom) :
    ((evalState p inputs).get hp).regs =
      ((evalState p.toStandardForm inputs).get hq).regs := by
  have ⟨hsteps, hhalted⟩ := evalState_spec p hp
  have ⟨hsteps', hhalted'⟩ := evalState_spec p.toStandardForm hq
  obtain ⟨s₂, hsteps₂, hhalted₂, hregs_eq⟩ := Steps.toStandardForm_halts hsteps hhalted
  rw [Steps.eq_of_halts hsteps' hhalted' hsteps₂ hhalted₂, hregs_eq]

/-- eval equality: both programs produce the same partial result.
@isnad1 id=eq.0h2v.s3.56806170d7cf from=translated src=- shape=e72b2eb9 vocab=b9d08885
-/
theorem eval_toStandardForm {p : Program} {inputs : List ℕ} :
    eval p inputs = eval p.toStandardForm inputs := by
  simp only [eval]
  apply Part.ext'
  · simp only [Part.map_Dom]
    exact Halts.toStandardForm_iff
  · intro hp hq
    have := Part.map_get (fun x : State => x.regs.output) (evalState p inputs) hp
    have := Part.map_get (fun x : State => x.regs.output) (evalState p.toStandardForm inputs) hq
    simp_all [Function.comp_def, evalState_toStandardForm_regs hp hq]

/-- A program is equivalent to its standard form.
@isnad1 id=equiv.0h1v.s3.884d1f83cd18 from=translated src=- shape=a365602c vocab=6a23589b
-/
theorem toStandardForm_equiv (p : Program) : p.toStandardForm ≈ p :=
  fun _ => eval_toStandardForm.symm

end Cslib.URM

end
