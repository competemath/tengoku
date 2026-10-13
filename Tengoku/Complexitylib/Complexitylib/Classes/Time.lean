/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine
public import Tengoku.Complexitylib.Complexitylib.Asymptotics

/-!
# Base time complexity classes

This file defines the parametric time complexity classes `DTIME(T)` and
`NTIME(T)`, the building blocks from which polynomial, exponential, and
randomized time classes are derived.

Both use `=O` (Mathlib's `IsBigO` lifted to `ℕ → ℕ`) to express asymptotic
bounds.
-/

@[expose] public section

namespace Complexity

/-- `DTIME(T)` is the class of languages decidable by a deterministic TM in
    time `O(T(n))` (AB Definition 1.6). The machine may have any number of
    work tapes. -/
def DTIME (T : ℕ → ℕ) : Set Language :=
  {L | ∃ (k : ℕ) (tm : TM k) (f : ℕ → ℕ),
    tm.DecidesInTime L f ∧ f =O T}

/-- `NTIME(T)` is the class of languages decidable by a nondeterministic TM in
    time `O(T(n))` (AB Definition 2.1). The machine may have any number of
    work tapes. -/
def NTIME (T : ℕ → ℕ) : Set Language :=
  {L | ∃ (k : ℕ) (tm : NTM k) (f : ℕ → ℕ),
    tm.DecidesInTime L f ∧ f =O T}

/-- **Complement class** constructor: `complClass C = {L | Lᶜ ∈ C}`.
    Used to uniformly define `coNP`, `coRP`, `coNL`, etc. -/
def complClass (C : Set Language) : Set Language :=
  {L | Lᶜ ∈ C}

/-- Membership in `complClass C` is exactly membership of the complement in `C`.
@isnad1 id=iff.0h2v.s4.b65a710d767a from=translated src=- shape=039e791e vocab=2697f70f
-/
@[simp] theorem mem_complClass {L : Language} {C : Set Language} :
    L ∈ complClass C ↔ Lᶜ ∈ C := Iff.rfl

/-- The complement class is involutive: `complClass (complClass C) = C`.
@isnad1 id=eq.0h1v.s3.a465ad6db2a2 from=translated src=- shape=e9e6e124 vocab=fbe8ad41
-/
theorem complClass_complClass (C : Set Language) : complClass (complClass C) = C := by
  ext L; simp [complClass]

/-- `complClass` is monotone.
@isnad1 id=le.1h2v.s4.ce17967962f0 from=translated src=- shape=4ad33e2d vocab=6ceb15e1
-/
theorem complClass_mono {C D : Set Language} (h : C ⊆ D) : complClass C ⊆ complClass D :=
  fun _ hL => h hL

end Complexity
