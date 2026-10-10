/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.MassProduction.Nonuniform.Menu
public import Tengoku.Complexitylib.Complexitylib.Algebraic.MassProduction.Nonuniform.CollisionTail
public import Tengoku.Complexitylib.Complexitylib.Algebraic.MassProduction.Scheduler

/-!
# Universal menus for a punctured-line scheduling phase

An occupied state is described by at most `capacity` previously accepted
lines and an ordered tuple of `active` targets. This is a finite description
space, including repetitions. A single fixed menu simultaneously contains a
half-clean candidate for every such state whenever the geometric packing
budget holds.

The theorem is nonuniform: the menu depends on the dimensions and request
counts, but is chosen before any occupied state or target tuple is supplied.
This module proves the menu guarantee, not the cost of its circuit evaluator.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform

open scoped BigOperators LinearAlgebra.Projectivization

/-- A bounded list of optional occupied lines together with ordered active
targets. Empty slots permit every smaller occupied-line collection. -/
abbrev PhaseState (Point Direction : Type*) (capacity active : Nat) :=
  (Fin capacity → Option (Point × Direction)) × (Fin active → Point)

/-- A phase state has at most `capacity * (1 + 3 * addressBits)` bits of
information when points and directions each fit in `addressBits` bits. -/
theorem cardPhaseState_le
    {Point Direction : Type*} [Fintype Point] [Fintype Direction]
    (capacity active addressBits : Nat) (activeLe : active ≤ capacity)
    (pointsSmall : Fintype.card Point ≤ 2 ^ addressBits)
    (directionsSmall : Fintype.card Direction ≤ 2 ^ addressBits) :
    Fintype.card (PhaseState Point Direction capacity active) ≤
      2 ^ (capacity * (1 + 3 * addressBits)) := by
  have oneLe : 1 ≤ (2 : Nat) ^ (2 * addressBits) := by
    have : 0 < (2 : Nat) ^ (2 * addressBits) := by positivity
    omega
  have pairSmall : Fintype.card Point * Fintype.card Direction ≤
      2 ^ (2 * addressBits) := by
    calc
      _ ≤ 2 ^ addressBits * 2 ^ addressBits := Nat.mul_le_mul pointsSmall directionsSmall
      _ = _ := by rw [two_mul, pow_add]
  have slotSmall : Fintype.card Point * Fintype.card Direction + 1 ≤
      2 ^ (1 + 2 * addressBits) := by
    calc
      _ ≤ 2 ^ (2 * addressBits) + 2 ^ (2 * addressBits) := Nat.add_le_add pairSmall oneLe
      _ = _ := by rw [pow_add]; simp; omega
  simp only [PhaseState, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_option]
  calc
    _ ≤ (2 ^ (1 + 2 * addressBits)) ^ capacity * (2 ^ addressBits) ^ capacity := by
      apply Nat.mul_le_mul (Nat.pow_le_pow_left slotSmall capacity)
      exact (Nat.pow_le_pow_left pointsSmall active).trans
        (Nat.pow_le_pow_right (by positivity) activeLe)
    _ = _ := by
      simp only [← pow_mul, ← pow_add]
      congr 1
      ring

variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]

/-- The actual occupied points described by the optional line slots. -/
noncomputable def phaseOccupied
    (state : PhaseState V (ℙ K V) capacity active) : Finset V := by
  classical
  exact Finset.univ.biUnion fun slot =>
    (state.1 slot).elim ∅ fun line => puncturedLine line.1 line.2

/-- A description with `capacity` slots occupies at most
`capacity * (|K| - 1)` points. Overlaps only reduce this number. -/
theorem cardPhaseOccupied_le
    (state : PhaseState V (ℙ K V) capacity active) :
    (phaseOccupied state).card ≤ capacity * (Nat.card K - 1) := by
  classical
  calc
    _ ≤ ∑ slot : Fin capacity,
        ((state.1 slot).elim ∅ fun line => puncturedLine line.1 line.2).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _slot : Fin capacity, (Nat.card K - 1) := by
      apply Finset.sum_le_sum
      intro slot _
      cases state.1 slot with
      | none => simp
      | some line => simp [card_puncturedLine]
    _ = _ := by simp

/-- A candidate is successful if at least half of the active requests are
clean, with rounding upward for an odd request count. -/
def HalfClean
    (state : PhaseState V (ℙ K V) capacity active)
    (candidate : Fin active → ℙ K V) : Prop :=
  active ≤ 2 * Nat.card {index : Fin active //
    Clean (fun index direction => puncturedLine (state.2 index) direction)
      (phaseOccupied state) candidate index}

/-- Evaluating every menu entry examines a number of candidate lines
linear in `capacity`, apart from the address-width factor. -/
theorem phaseMenuCandidateCount_le
    (capacity active addressBits : Nat) (activeLe : active ≤ capacity) :
    (capacity * (1 + 3 * addressBits) / active + 1) * active ≤
      capacity * (2 + 3 * addressBits) := by
  calc
    _ = (capacity * (1 + 3 * addressBits) / active) * active + active := by ring
    _ ≤ capacity * (1 + 3 * addressBits) + capacity :=
      Nat.add_le_add (Nat.div_mul_le_self _ _) activeLe
    _ = _ := by ring

end Algebraic.MassProduction.Nonuniform
