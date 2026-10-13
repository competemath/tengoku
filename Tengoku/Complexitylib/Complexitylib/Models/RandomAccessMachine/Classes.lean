/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.RandomAccessMachine.Classes.Defs

/-!
# Random-access-machine complexity classes

This surface exposes the logarithmic-cost RAM time and space classes and their
elementary monotonicity properties.
-/

public section

namespace Complexity

namespace RAM

/-- Deciding in logarithmic time is monotone in the time bound.
@isnad1 id=decidesi.2h4v.s5.54335a86db50 from=translated src=- shape=726f958c vocab=93d6f044
-/
theorem Program.DecidesInTime.mono {P : Program} {L : Language} {T T' : ℕ → ℕ}
    (hle : ∀ m, T m ≤ T' m) (h : P.DecidesInTime L T) : P.DecidesInTime L T' := by
  intro x
  obtain ⟨fuel, hhalt, hcost, hyes, hno⟩ := h x
  exact ⟨fuel, hhalt, hcost.trans (hle x.length), hyes, hno⟩

/-- Deciding in logarithmic space is monotone in the space bound.
@isnad1 id=decidesi.2h4v.s5.c4b44ae09890 from=translated src=- shape=726f958c vocab=96639558
-/
theorem Program.DecidesInSpace.mono {P : Program} {L : Language} {S S' : ℕ → ℕ}
    (hle : ∀ m, S m ≤ S' m) (h : P.DecidesInSpace L S) :
    P.DecidesInSpace L S' := by
  intro x
  obtain ⟨fuel, hhalt, hspace, hyes, hno⟩ := h x
  exact ⟨fuel, hhalt, hspace.trans (hle x.length), hyes, hno⟩

end RAM

end Complexity
