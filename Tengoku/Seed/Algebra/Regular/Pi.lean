/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Regular.SMul

/-!
# Results about `IsRegular` and pi types
-/

public section

variable {ι α : Type*} {R : ι → Type*}

namespace Pi

section
variable [∀ i, Mul (R i)]

/--
@isnad1 id=iff.0h3v.s5.f4bf5288cafd from=seed src=0 shape=bbebe99d vocab=25f20bf7
-/
@[to_additive (attr := simp)]
theorem isLeftRegular_iff {a : ∀ i, R i} : IsLeftRegular a ↔ ∀ i, IsLeftRegular (a i) :=
  have (i : _) : Nonempty (R i) := ⟨a i⟩; Pi.map_injective

/--
@isnad1 id=iff.0h3v.s5.a6d91825711c from=seed src=0 shape=bbebe99d vocab=1f0b9fee
-/
@[to_additive (attr := simp)]
theorem isRightRegular_iff {a : ∀ i, R i} : IsRightRegular a ↔ ∀ i, IsRightRegular (a i) :=
  have (i : _) : Nonempty (R i) := ⟨a i⟩; .symm <| Pi.map_injective.symm

/--
@isnad1 id=iff.0h3v.s5.f00b9626b3a1 from=seed src=0 shape=bbebe99d vocab=17657e9d
-/
@[to_additive (attr := simp)]
theorem isRegular_iff {a : ∀ i, R i} : IsRegular a ↔ ∀ i, IsRegular (a i) := by
  simp [_root_.isRegular_iff, forall_and]

end

/--
@isnad1 id=iff.0h4v.s5.c66b4fa61f16 from=seed src=0 shape=18828062 vocab=dc6675e5
-/
@[simp]
theorem isSMulRegular_iff [∀ i, SMul α (R i)] {r : α} [∀ i, Nonempty (R i)] :
    IsSMulRegular (∀ i, R i) r ↔ ∀ i, IsSMulRegular (R i) r :=
  Pi.map_injective

end Pi
