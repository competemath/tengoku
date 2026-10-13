/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Subroutines.Counter

/-!
# Unary registers

A *register* is a work tape holding a natural number in unary: cells `1..v`
hold `1`, everything beyond is blank, and the head is parked at cell 1. All
arithmetic in the Cook–Levin reduction emitter (`docs/A5-ReductionEmitter.md`)
is over registers — the CNF encoding is unary, so no binary arithmetic is
ever needed.

`IsReg` strengthens `Tape.HasUnaryCounter` with the cell-0 sentinel and
all-blanks-beyond, making registers literally preserved by parked no-op
actions and stable under the combinator phase transitions.

## Main definitions

- `TM.Parked` — a tape whose head is off `▷` and which has no spurious `▷`s
- `TM.IsReg` — the register predicate

## Main results

- `TM.IsReg.parked`, `TM.IsReg.hasUnaryCounter` — bridges
- `TM.reg_zero_init_bumped` — a freshly bumped blank tape is `IsReg 0`
-/

@[expose] public section

namespace Complexity

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Parked tapes
-- ════════════════════════════════════════════════════════════════════════

/-- A tape parked for preservation: head off `▷` (so `idleDir` stays put and
    `δ_right_of_start` is moot) and no `▷` outside cell 0 (so `readBackWrite`
    writes back the read symbol verbatim). Machines that do not use a tape
    keep it parked and literally unchanged. -/
def Parked (t : Tape) : Prop :=
  1 ≤ t.head ∧ ∀ j, 1 ≤ j → t.cells j ≠ Γ.start

/-- A parked tape never reads the start symbol `▷`.
@isnad1 id=ne.1h1v.s3.8412d9138523 from=translated src=- shape=cd8a2b58 vocab=061662d1
-/
theorem Parked.read_ne_start {t : Tape} (h : Parked t) : t.read ≠ Γ.start :=
  h.2 t.head h.1

/-- A parked tape is untouched by the no-op action `writeAndMove (readBackWrite
    read) (idleDir read)`.
@isnad1 id=eq.1h1v.s4.df7bf89fd2b7 from=translated src=- shape=bd265543 vocab=524b3989
-/
theorem Parked.writeAndMove_readBack_idle {t : Tape} (h : Parked t) :
    t.writeAndMove (readBackWrite t.read) (idleDir t.read) = t :=
  Tape.writeAndMove_readBack_idle_of_ne_start t h.read_ne_start

/-- A parked tape's head does not move under `idleDir`.
@isnad1 id=eq.1h1v.s3.8a70cc4f4df8 from=translated src=- shape=500ba717 vocab=23750e26
-/
theorem Parked.move_idle {t : Tape} (h : Parked t) :
    t.move (idleDir t.read) = t := by
  rw [idleDir, ite_eq_right h.read_ne_start]
  rfl

/-- Parked tapes pass through combinator phase boundaries unchanged.
@isnad1 id=eq.1h1v.s3.f9656d14c61b from=translated src=- shape=5b131564 vocab=51270b42
-/
theorem Parked.transitionTape_eq_self {t : Tape} (h : Parked t) : transitionTape t = t :=
  TM.transitionTape_eq_self h.read_ne_start

/-- Parked input tapes pass through combinator phase boundaries unchanged.
@isnad1 id=eq.1h1v.s3.1b0a058e0303 from=translated src=- shape=5b131564 vocab=09cbcd58
-/
theorem Parked.transitionInput_eq_self {t : Tape} (h : Parked t) : transitionInput t = t :=
  TM.transitionInput_eq_self h.read_ne_start

-- ════════════════════════════════════════════════════════════════════════
-- Registers
-- ════════════════════════════════════════════════════════════════════════

/-- **Register.** The tape holds `v` in unary: `▷` at cell 0, `1` at cells
    `1..v`, blank everywhere beyond, head parked at cell 1. -/
def IsReg (v : ℕ) (t : Tape) : Prop :=
  t.head = 1 ∧
  t.cells 0 = Γ.start ∧
  (∀ i, i < v → t.cells (i + 1) = Γ.one) ∧
  (∀ j, v + 1 ≤ j → t.cells j = Γ.blank)

namespace IsReg

/-- A register tape's head is parked at cell 1.
@isnad1 id=eq.1h2v.s4.fd191b1a5f02 from=translated src=- shape=4331d232 vocab=ed0f9dc5
-/
theorem head_eq {v : ℕ} {t : Tape} (h : IsReg v t) : t.head = 1 := h.1

/-- A register tape's cell 0 holds the sentinel `▷`.
@isnad1 id=eq.1h2v.s4.1a3a453bbe47 from=translated src=- shape=961b7c31 vocab=01571a52
-/
theorem cell0 {v : ℕ} {t : Tape} (h : IsReg v t) : t.cells 0 = Γ.start := h.2.1

/-- Cells `1..v` of a register holding `v` contain `1`.
@isnad1 id=eq.2h3v.s5.d102f7e69129 from=translated src=- shape=f22f5eaa vocab=2364f088
-/
theorem cells_one {v : ℕ} {t : Tape} (h : IsReg v t) {i : ℕ} (hi : i < v) :
    t.cells (i + 1) = Γ.one := h.2.2.1 i hi

/-- Cells beyond position `v` of a register holding `v` are blank.
@isnad1 id=eq.2h3v.s5.065d7df5907b from=translated src=- shape=89b80a73 vocab=2755a36b
-/
theorem cells_blank {v : ℕ} {t : Tape} (h : IsReg v t) {j : ℕ} (hj : v + 1 ≤ j) :
    t.cells j = Γ.blank := h.2.2.2 j hj

/-- Register cells off the sentinel are `1` or blank — never `▷`.
@isnad1 id=ne.2h3v.s4.47a341a94243 from=translated src=- shape=4e6db6ab vocab=25cce08c
-/
theorem cells_ne_start {v : ℕ} {t : Tape} (h : IsReg v t) {j : ℕ} (hj : 1 ≤ j) :
    t.cells j ≠ Γ.start := by
  rcases Nat.lt_or_ge j (v + 1) with hlt | hge
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [h.cells_one (by omega)]; decide
  · rw [h.cells_blank hge]; decide

/-- A register tape is parked.
@isnad1 id=parked.1h2v.s3.11ba3d3f453a from=translated src=- shape=3a03dd3e vocab=8c25f127
-/
theorem parked {v : ℕ} {t : Tape} (h : IsReg v t) : Parked t :=
  ⟨by rw [h.head_eq], fun _ hj => h.cells_ne_start hj⟩

/-- A register is a unary counter (the weaker shape used by the counter
    subroutines).
@isnad1 id=hasunary.1h2v.s3.ed0450808fc9 from=translated src=- shape=01c45f1c vocab=bd1ba75d
-/
theorem hasUnaryCounter {v : ℕ} {t : Tape} (h : IsReg v t) :
    t.HasUnaryCounter v :=
  ⟨h.head_eq, fun _ hi => h.cells_one hi, h.cells_blank (le_refl _)⟩

/-- The register's read: `1` when nonempty, blank when zero.
@isnad1 id=eq.1h2v.s4.cac728eb33e4 from=translated src=- shape=1c083c12 vocab=52a2889c
-/
theorem read_eq {v : ℕ} {t : Tape} (h : IsReg v t) :
    t.read = if v = 0 then Γ.blank else Γ.one := by
  rw [Tape.read, h.head_eq]
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [ite_eq_left rfl]; exact h.cells_blank (le_refl _)
  · rw [ite_eq_right (by omega)]; exact h.cells_one hv

end IsReg

/-- A blank tape with the head bumped to cell 1 is the zero register.
@isnad1 id=isreg.0h0v.s4.75bb7910d831 from=translated src=- shape=aaa93c5a vocab=0a285ab1
-/
theorem reg_zero_init_bumped : IsReg 0 { head := 1, cells := (Tape.init []).cells } := by
  refine ⟨rfl, by simp [Tape.init], fun _ hi => by omega, fun j hj => ?_⟩
  show (Tape.init []).cells j = Γ.blank
  simp only [Tape.init]
  rw [ite_eq_right (by omega : ¬ j = 0)]
  simp

-- ════════════════════════════════════════════════════════════════════════
-- The canonical register tape
-- ════════════════════════════════════════════════════════════════════════

/-- Canonical register cells holding `v` in unary. -/
def regCells (v : ℕ) : ℕ → Γ := fun j =>
  if j = 0 then Γ.start else if j ≤ v then Γ.one else Γ.blank

/-- The canonical register tape holding `v`. -/
def regTape (v : ℕ) : Tape := ⟨1, regCells v⟩

/-- The canonical register tape's head sits at cell 1.
@isnad1 id=eq.0h1v.s3.e1f3a1ea491b from=translated src=- shape=3c43d5e2 vocab=304ede79
-/
@[simp] theorem regT_head (v : ℕ) : (regTape v).head = 1 := rfl

/-- The canonical register tape's cells are `regCells v`.
@isnad1 id=eq.0h1v.s3.26a73d03bfc3 from=translated src=- shape=57cb08ec vocab=b357874a
-/
@[simp] theorem regT_cells (v : ℕ) : (regTape v).cells = regCells v := rfl

/-- Cell 0 of the canonical register cells is the sentinel `▷`.
@isnad1 id=eq.0h1v.s3.d8c8b131bed8 from=translated src=- shape=a62063d2 vocab=a669973f
-/
@[simp] theorem regCells_zero (v : ℕ) : regCells v 0 = Γ.start := rfl

/-- Cells `1..v` of the canonical register cells for `v` hold `1`.
@isnad1 id=eq.2h2v.s4.8aa193f6a6aa from=translated src=- shape=3dd9de8e vocab=1dc969e9
-/
theorem regCells_one {v j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ v) : regCells v j = Γ.one := by
  rw [regCells, ite_eq_right (by omega), ite_eq_left h2]

/-- Cells beyond position `v` of the canonical register cells for `v` are blank.
@isnad1 id=eq.1h2v.s4.d9c8965cccb4 from=translated src=- shape=5d5f7114 vocab=afffa0ed
-/
theorem regCells_blank {v j : ℕ} (h : v + 1 ≤ j) : regCells v j = Γ.blank := by
  rw [regCells, ite_eq_right (by omega), ite_eq_right (by omega)]

/-- Register cells away from the sentinel are never `▷`.
@isnad1 id=ne.1h2v.s4.4e3b5adccec1 from=translated src=- shape=6a49379f vocab=216b97e2
-/
theorem regCells_ne_start {v j : ℕ} (hj : 1 ≤ j) :
    regCells v j ≠ Γ.start := by
  rw [regCells, ite_eq_right (by omega)]
  split <;> decide

/-- The canonical register tape `regTape v` satisfies `IsReg v`.
@isnad1 id=isreg.0h1v.s2.33d6695b47d0 from=translated src=- shape=9d44d080 vocab=e31a2f44
-/
theorem reg_regT (v : ℕ) : IsReg v (regTape v) :=
  ⟨rfl, rfl, fun _ hi => by rw [regT_cells]; exact regCells_one (by omega) (by omega),
   fun _ hj => by rw [regT_cells]; exact regCells_blank hj⟩

/-- **A register's tape is canonical**: the `IsReg` predicate pins every cell and
    the head, so it is an equation. -/
theorem IsReg.eq_regT {v : ℕ} {t : Tape} (h : IsReg v t) : t = regTape v := by
  refine Tape.ext h.head_eq ?_
  funext j
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [h.cell0]; rfl
  · rcases Nat.lt_or_ge v j with hlt | hge
    · rw [h.cells_blank (by omega), regT_cells]
      exact (regCells_blank (by omega)).symm
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rw [h.cells_one (by omega), regT_cells]
      exact (regCells_one (by omega) (by omega)).symm

/-- The canonical register tape is parked.
@isnad1 id=parked.0h1v.s2.4c311826918b from=translated src=- shape=76a08d12 vocab=d1fe50ad
-/
theorem parked_regTape (v : ℕ) : Parked (regTape v) := (reg_regT v).parked

/-- Register cells with the head anywhere off `▷` form a parked tape.
@isnad1 id=parked.1h2v.s4.77588335caff from=translated src=- shape=932fc818 vocab=e834204f
-/
theorem parked_regCells {h v : ℕ} (hh : 1 ≤ h) :
    Parked (⟨h, regCells v⟩ : Tape) := by
  exact ⟨hh, fun _ hj => regCells_ne_start hj⟩

/-- Writing the next mark turns `regCells d` into `regCells (d + 1)`.
@isnad1 id=eq.0h1v.s5.066974e6b5f0 from=translated src=- shape=f34be5dc vocab=294d85b0
-/
theorem regCells_update_succ (d : ℕ) :
    Function.update (regCells d) (d + 1) Γ.one = regCells (d + 1) := by
  funext j
  rw [Function.update_apply]
  split
  · next h =>
    subst h
    exact (regCells_one (by omega) (by omega)).symm
  · next h =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rfl
    · rcases Nat.lt_or_ge d j with hlt | hge
      · rw [regCells_blank (by omega), regCells_blank (by omega)]
      · rw [regCells_one (by omega) (by omega), regCells_one (by omega) (by omega)]

/-- Erasing the final mark turns `regCells (d + 1)` into `regCells d`.
@isnad1 id=eq.0h1v.s5.30df006822ac from=translated src=- shape=bc064850 vocab=d6a0058d
-/
theorem regCells_update_blank_succ (d : ℕ) :
    Function.update (regCells (d + 1)) (d + 1) Γ.blank = regCells d := by
  funext j
  rw [Function.update_apply]
  split
  · next hj =>
    subst hj
    exact (regCells_blank (by omega)).symm
  · next hj =>
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · rfl
    · rcases Nat.lt_or_ge d j with hlt | hge
      · rw [regCells_blank (by omega), regCells_blank (by omega)]
      · rw [regCells_one (by omega) (by omega), regCells_one (by omega) (by omega)]

end TM

end Complexity
