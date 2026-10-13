/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Combinators.Internal.Generic
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Subroutines.BinaryFor.Defs

/-!
# Canonical binary count-up loops — control proofs

This module supplies the local proof interface for `TM.binaryForTM`. It lifts
runs of the composite body-plus-successor iteration through the outer control
state and gives exact, full-frame transition lemmas for scanning, rewinding,
entering an iteration, and returning from a completed iteration.

The canonical multi-step comparison run and loop induction are intentionally
left to later proof layers.
-/

@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Embed a composite iteration configuration into the iteration phase of
`binaryForTM`. -/
def binaryForIterationWrap (body : TM n) (counterIdx limitIdx : Fin n)
    (c : Cfg n (binaryForIterationTM body counterIdx).Q) :
    Cfg n (binaryForTM body counterIdx limitIdx).Q :=
  { state := .inr c.state
    input := c.input
    work := c.work
    output := c.output }

/-- Every nonhalting composite-iteration step is simulated exactly by one
`binaryForTM` step.
@isnad1 id=eq.1h6v.s6.7c8bfb22f992 from=translated src=- shape=d4a00967 vocab=a8d42bd3
-/
theorem binaryForTM_iteration_step_internal (body : TM n)
    (counterIdx limitIdx : Fin n)
    {c c' : Cfg n (binaryForIterationTM body counterIdx).Q}
    (hstep : (binaryForIterationTM body counterIdx).step c = some c') :
    (binaryForTM body counterIdx limitIdx).step
        (binaryForIterationWrap body counterIdx limitIdx c) =
      some (binaryForIterationWrap body counterIdx limitIdx c') := by
  have hne : c.state ≠ (binaryForIterationTM body counterIdx).qhalt :=
    state_ne_qhalt_of_step hstep
  rw [TM.step, ite_eq_right (by simp [binaryForIterationWrap, binaryForTM])]
  simp only [binaryForIterationWrap, binaryForTM, hne, ↓reduceIte]
  rw [TM.step, ite_eq_right hne] at hstep
  injection hstep with hstep'
  subst hstep'
  rfl

/-- Exact runs of the composite iteration lift through the iteration phase of
`binaryForTM`.
@isnad1 id=reachesi.1h7v.s5.16c002f6e582 from=translated src=- shape=22e127c2 vocab=a42773fa
-/
theorem binaryForTM_iteration_reachesIn_internal (body : TM n)
    (counterIdx limitIdx : Fin n)
    {t : ℕ} {c c' : Cfg n (binaryForIterationTM body counterIdx).Q}
    (hreach : (binaryForIterationTM body counterIdx).reachesIn t c c') :
    (binaryForTM body counterIdx limitIdx).reachesIn t
      (binaryForIterationWrap body counterIdx limitIdx c)
      (binaryForIterationWrap body counterIdx limitIdx c') :=
  reachesIn_map (binaryForIterationWrap body counterIdx limitIdx)
    (fun _ _ => binaryForTM_iteration_step_internal body counterIdx limitIdx) hreach

/-- Away from the common terminating blank, one scanner step compares the
current symbols and advances both designated tapes, preserving the full
off-start frame.
@isnad1 id=eq.6h6v.s8.e05da2fed370 from=translated src=- shape=105b864b vocab=bda93806
-/
theorem binaryForTM_step_scan_internal (body : TM n)
    (counterIdx limitIdx : Fin n) (hne : counterIdx ≠ limitIdx)
    (equalSoFar : Bool) (c : Cfg n (binaryForTM body counterIdx limitIdx).Q)
    (hstate : c.state = .inl (.scan equalSoFar))
    (hmore : ¬((c.work counterIdx).read = Γ.blank ∧
      (c.work limitIdx).read = Γ.blank))
    (hinput : c.input.read ≠ Γ.start)
    (hwork : ∀ i, (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (binaryForTM body counterIdx limitIdx).step c = some
      { state := .inl (.scan
          (equalSoFar && decide ((c.work counterIdx).read = (c.work limitIdx).read)))
        input := c.input
        work := Function.update
          (Function.update c.work counterIdx ((c.work counterIdx).move Dir3.right))
          limitIdx ((c.work limitIdx).move Dir3.right)
        output := c.output } := by
  rw [TM.step, ite_eq_right (by rw [hstate]; simp [binaryForTM])]
  simp only [binaryForTM, hstate]
  rw [ite_eq_right hmore]
  dsimp only
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinput
  · funext i
    by_cases hic : i = counterIdx
    · subst i
      rw [ite_eq_left rfl, Function.update_of_ne hne, Function.update_self,
        writeAndMove_readBack _ (hwork counterIdx)]
    · rw [ite_eq_right hic]
      by_cases hil : i = limitIdx
      · subst i
        rw [ite_eq_left rfl, Function.update_self,
          writeAndMove_readBack _ (hwork limitIdx)]
      · rw [ite_eq_right hil, Function.update_of_ne hil, Function.update_of_ne hic]
        exact transitionTape_eq_self (hwork i)
  · exact transitionTape_eq_self houtput

/-- At the common terminating blank, one scanner step enters rewind and moves
both designated tapes left, preserving the full off-start frame.
@isnad1 id=eq.7h6v.s8.4e19feb51065 from=translated src=- shape=f075bafe vocab=1b56b79e
-/
theorem binaryForTM_step_scan_blank_internal (body : TM n)
    (counterIdx limitIdx : Fin n) (hne : counterIdx ≠ limitIdx)
    (equalSoFar : Bool) (c : Cfg n (binaryForTM body counterIdx limitIdx).Q)
    (hstate : c.state = .inl (.scan equalSoFar))
    (hcounter : (c.work counterIdx).read = Γ.blank)
    (hlimit : (c.work limitIdx).read = Γ.blank)
    (hinput : c.input.read ≠ Γ.start)
    (hwork : ∀ i, (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (binaryForTM body counterIdx limitIdx).step c = some
      { state := .inl (.rewind equalSoFar)
        input := c.input
        work := Function.update
          (Function.update c.work counterIdx ((c.work counterIdx).move Dir3.left))
          limitIdx ((c.work limitIdx).move Dir3.left)
        output := c.output } := by
  rw [TM.step, ite_eq_right (by rw [hstate]; simp [binaryForTM])]
  simp only [binaryForTM, hstate]
  rw [ite_eq_left ⟨hcounter, hlimit⟩]
  dsimp only
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinput
  · funext i
    by_cases hic : i = counterIdx
    · subst i
      rw [ite_eq_left rfl, Function.update_of_ne hne, Function.update_self,
        writeAndMove_readBack _ (hwork counterIdx)]
    · rw [ite_eq_right hic]
      by_cases hil : i = limitIdx
      · subst i
        rw [ite_eq_left rfl, Function.update_self,
          writeAndMove_readBack _ (hwork limitIdx)]
      · rw [ite_eq_right hil, Function.update_of_ne hil, Function.update_of_ne hic]
        exact transitionTape_eq_self (hwork i)
  · exact transitionTape_eq_self houtput

/-- One ordinary rewind step moves both designated tapes left, preserving the
full off-start frame.
@isnad1 id=eq.5h6v.s7.fc3507d07fa1 from=translated src=- shape=31e477e8 vocab=fa5ee357
-/
theorem binaryForTM_step_rewind_internal (body : TM n)
    (counterIdx limitIdx : Fin n) (hne : counterIdx ≠ limitIdx)
    (equalSoFar : Bool) (c : Cfg n (binaryForTM body counterIdx limitIdx).Q)
    (hstate : c.state = .inl (.rewind equalSoFar))
    (hinput : c.input.read ≠ Γ.start)
    (hwork : ∀ i, (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (binaryForTM body counterIdx limitIdx).step c = some
      { state := .inl (.rewind equalSoFar)
        input := c.input
        work := Function.update
          (Function.update c.work counterIdx ((c.work counterIdx).move Dir3.left))
          limitIdx ((c.work limitIdx).move Dir3.left)
        output := c.output } := by
  rw [TM.step, ite_eq_right (by rw [hstate]; simp [binaryForTM])]
  have hnotboth : ¬((c.work counterIdx).read = Γ.start ∧
      (c.work limitIdx).read = Γ.start) := by
    intro h
    exact hwork counterIdx h.1
  simp only [binaryForTM, hstate]
  rw [ite_eq_right hnotboth]
  dsimp only
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinput
  · funext i
    by_cases hic : i = counterIdx
    · subst i
      rw [ite_eq_left rfl, Function.update_of_ne hne, Function.update_self,
        writeAndMove_readBack _ (hwork counterIdx)]
      simp [moveLeftDir, hwork counterIdx]
    · rw [ite_eq_right hic]
      by_cases hil : i = limitIdx
      · subst i
        rw [ite_eq_left rfl, Function.update_self,
          writeAndMove_readBack _ (hwork limitIdx)]
        simp [moveLeftDir, hwork limitIdx]
      · rw [ite_eq_right hil, Function.update_of_ne hil, Function.update_of_ne hic]
        exact transitionTape_eq_self (hwork i)
  · exact transitionTape_eq_self houtput

/-- When an equal comparison rewinds to both left markers, one preserving
step returns both designated heads to cell one and halts the loop.
@isnad1 id=eq.9h5v.s8.649bd656f32a from=translated src=- shape=bd322c23 vocab=da5fba58
-/
theorem binaryForTM_step_rewind_equal_internal (body : TM n)
    (counterIdx limitIdx : Fin n) (hne : counterIdx ≠ limitIdx)
    (c : Cfg n (binaryForTM body counterIdx limitIdx).Q)
    (hstate : c.state = .inl (.rewind true))
    (hcounter : (c.work counterIdx).read = Γ.start)
    (hlimit : (c.work limitIdx).read = Γ.start)
    (hcounterHead : (c.work counterIdx).head = 0)
    (hlimitHead : (c.work limitIdx).head = 0)
    (hinput : c.input.read ≠ Γ.start)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx →
      (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (binaryForTM body counterIdx limitIdx).step c = some
      { state := .inl .done
        input := c.input
        work := Function.update
          (Function.update c.work counterIdx ((c.work counterIdx).move Dir3.right))
          limitIdx ((c.work limitIdx).move Dir3.right)
        output := c.output } := by
  rw [TM.step, ite_eq_right (by rw [hstate]; simp [binaryForTM])]
  simp only [binaryForTM, hstate]
  rw [ite_eq_left ⟨hcounter, hlimit⟩]
  dsimp only
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinput
  · funext i
    by_cases hic : i = counterIdx
    · subst i
      rw [ite_eq_left rfl, Function.update_of_ne hne, Function.update_self]
      show (((c.work counterIdx).write _).move Dir3.right) =
        (c.work counterIdx).move Dir3.right
      rw [Tape.write, ite_eq_left hcounterHead]
    · rw [ite_eq_right hic]
      by_cases hil : i = limitIdx
      · subst i
        rw [ite_eq_left rfl, Function.update_self]
        show (((c.work limitIdx).write _).move Dir3.right) =
          (c.work limitIdx).move Dir3.right
        rw [Tape.write, ite_eq_left hlimitHead]
      · rw [ite_eq_right hil, Function.update_of_ne hil, Function.update_of_ne hic]
        exact transitionTape_eq_self (hother i hic hil)
  · exact transitionTape_eq_self houtput

/-- When an unequal comparison rewinds to both left markers, one preserving
step returns both designated heads to cell one and enters the composite
iteration.
@isnad1 id=eq.9h5v.s8.9b929c3e1bd0 from=translated src=- shape=41e1acd7 vocab=bac584d2
-/
theorem binaryForTM_step_rewind_unequal_internal (body : TM n)
    (counterIdx limitIdx : Fin n) (hne : counterIdx ≠ limitIdx)
    (c : Cfg n (binaryForTM body counterIdx limitIdx).Q)
    (hstate : c.state = .inl (.rewind false))
    (hcounter : (c.work counterIdx).read = Γ.start)
    (hlimit : (c.work limitIdx).read = Γ.start)
    (hcounterHead : (c.work counterIdx).head = 0)
    (hlimitHead : (c.work limitIdx).head = 0)
    (hinput : c.input.read ≠ Γ.start)
    (hother : ∀ i, i ≠ counterIdx → i ≠ limitIdx →
      (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (binaryForTM body counterIdx limitIdx).step c = some
      { state := .inr (binaryForIterationTM body counterIdx).qstart
        input := c.input
        work := Function.update
          (Function.update c.work counterIdx ((c.work counterIdx).move Dir3.right))
          limitIdx ((c.work limitIdx).move Dir3.right)
        output := c.output } := by
  rw [TM.step, ite_eq_right (by rw [hstate]; simp [binaryForTM])]
  simp only [binaryForTM, hstate]
  rw [ite_eq_left ⟨hcounter, hlimit⟩]
  dsimp only
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinput
  · funext i
    by_cases hic : i = counterIdx
    · subst i
      rw [ite_eq_left rfl, Function.update_of_ne hne, Function.update_self]
      show (((c.work counterIdx).write _).move Dir3.right) =
        (c.work counterIdx).move Dir3.right
      rw [Tape.write, ite_eq_left hcounterHead]
    · rw [ite_eq_right hic]
      by_cases hil : i = limitIdx
      · subst i
        rw [ite_eq_left rfl, Function.update_self]
        show (((c.work limitIdx).write _).move Dir3.right) =
          (c.work limitIdx).move Dir3.right
        rw [Tape.write, ite_eq_left hlimitHead]
      · rw [ite_eq_right hil, Function.update_of_ne hil, Function.update_of_ne hic]
        exact transitionTape_eq_self (hother i hic hil)
  · exact transitionTape_eq_self houtput

/-- A halted composite iteration takes one preserving outer seam step back to
a fresh equality scan.
@isnad1 id=eq.4h5v.s7.027377576d5a from=translated src=- shape=9e222ef8 vocab=3f5d01c4
-/
theorem binaryForTM_step_iteration_halt_internal (body : TM n)
    (counterIdx limitIdx : Fin n)
    (c : Cfg n (binaryForIterationTM body counterIdx).Q)
    (hhalt : (binaryForIterationTM body counterIdx).halted c)
    (hinput : c.input.read ≠ Γ.start)
    (hwork : ∀ i, (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (binaryForTM body counterIdx limitIdx).step
        (binaryForIterationWrap body counterIdx limitIdx c) = some
      { state := .inl (.scan true)
        input := c.input
        work := c.work
        output := c.output } := by
  rw [TM.step, ite_eq_right (by simp [binaryForIterationWrap, binaryForTM])]
  simp only [binaryForIterationWrap, binaryForTM, hhalt, allReadBack, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinput
  · funext i
    exact transitionTape_eq_self (hwork i)
  · exact transitionTape_eq_self houtput

end TM

end Complexity
