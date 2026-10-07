/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Group.Units.Basic
public import Tengoku.Seed.Algebra.Order.Monoid.Unbundled.Basic

/-!
# Lemmas for units in an ordered monoid
-/

public section

variable {M : Type*} [Monoid M] [LE M]

namespace Units

section MulLeftMono
variable [MulLeftMono M] (u : Mˣ) {a b : M}

/--
@isnad1 id=mullecan.0h2v.s5.54ee87430022 from=seed src=0 shape=2a2f7329 vocab=39eea6a5
-/
theorem mulLECancellable_val : MulLECancellable (↑u : M) := fun _ _ h ↦ by
  simpa using mul_le_mul_right h ↑u⁻¹

private theorem mul_le_mul_iff_left : u * a ≤ u * b ↔ a ≤ b :=
  u.mulLECancellable_val.mul_le_mul_iff_left

/--
@isnad1 id=iff.0h4v.s6.c635b99fde16 from=seed src=0 shape=a9a365f4 vocab=05c4a054
-/
theorem inv_mul_le_iff : u⁻¹ * a ≤ b ↔ a ≤ u * b := by
  rw [← u.mul_le_mul_iff_left, mul_inv_cancel_left]

/--
@isnad1 id=iff.0h4v.s6.366be0fb2d67 from=seed src=0 shape=29c4e1c5 vocab=05c4a054
-/
theorem le_inv_mul_iff : a ≤ u⁻¹ * b ↔ u * a ≤ b := by
  rw [← u.mul_le_mul_iff_left, mul_inv_cancel_left]

/--
@isnad1 id=iff.0h2v.s6.dba951ebe425 from=seed src=0 shape=7e667b50 vocab=bf27df4b
-/
@[simp] theorem one_le_inv : (1 : M) ≤ u⁻¹ ↔ (u : M) ≤ 1 := by
  rw [← u.mul_le_mul_iff_left, mul_one, mul_inv]

/--
@isnad1 id=iff.0h2v.s6.5bcda9272deb from=seed src=0 shape=04a542bf vocab=bf27df4b
-/
@[simp] theorem inv_le_one : u⁻¹ ≤ (1 : M) ↔ (1 : M) ≤ u := by
  rw [← u.mul_le_mul_iff_left, mul_one, mul_inv]

/--
@isnad1 id=iff.0h3v.s6.6811895ec70d from=seed src=0 shape=59f25db6 vocab=05c4a054
-/
theorem one_le_inv_mul : 1 ≤ u⁻¹ * a ↔ u ≤ a := by
  rw [u.le_inv_mul_iff, mul_one]

/--
@isnad1 id=iff.0h3v.s6.a62dbefe4424 from=seed src=0 shape=860605b0 vocab=05c4a054
-/
theorem inv_mul_le_one : u⁻¹ * a ≤ 1 ↔ a ≤ u := by
  rw [u.inv_mul_le_iff, mul_one]

alias ⟨le_mul_of_inv_mul_le, inv_mul_le_of_le_mul⟩ := inv_mul_le_iff
alias ⟨mul_le_of_le_inv_mul, le_inv_mul_of_mul_le⟩ := le_inv_mul_iff
alias ⟨le_of_one_le_inv, one_le_inv_of_le⟩ := one_le_inv
alias ⟨le_of_inv_le_one, inv_le_one_of_le⟩ := inv_le_one
alias ⟨le_of_one_le_inv_mul, one_le_inv_mul_of_le⟩ := one_le_inv_mul
alias ⟨le_of_inv_mul_le_one, inv_mul_le_one_of_le⟩ := inv_mul_le_one

end MulLeftMono

section MulRightMono
variable [MulRightMono M] {a b : M} (u : Mˣ)

private theorem mul_le_mul_iff_right : a * u ≤ b * u ↔ a ≤ b :=
  ⟨(by simpa using mul_le_mul_left · ↑u⁻¹), (mul_le_mul_left · _)⟩

/--
@isnad1 id=iff.0h4v.s6.befa6afb2272 from=seed src=0 shape=9118c41e vocab=5a796024
-/
theorem mul_inv_le_iff : a * u⁻¹ ≤ b ↔ a ≤ b * u := by
  rw [← u.mul_le_mul_iff_right, u.inv_mul_cancel_right]

/--
@isnad1 id=iff.0h4v.s6.43af3723388b from=seed src=0 shape=e13cf396 vocab=5a796024
-/
theorem le_mul_inv_iff : a ≤ b * u⁻¹ ↔ a * u ≤ b := by
  rw [← u.mul_le_mul_iff_right, inv_mul_cancel_right]

/--
@isnad1 id=iff.0h3v.s6.bd86323e035d from=seed src=0 shape=7d47bb83 vocab=5a796024
-/
theorem one_le_mul_inv : 1 ≤ a * u⁻¹ ↔ u ≤ a := by
  rw [u.le_mul_inv_iff, one_mul]

/--
@isnad1 id=iff.0h3v.s6.c6ef0247bd1d from=seed src=0 shape=7778f55e vocab=5a796024
-/
theorem mul_inv_le_one : a * u⁻¹ ≤ 1 ↔ a ≤ u := by
  rw [u.mul_inv_le_iff, one_mul]

alias ⟨le_mul_of_mul_inv_le, mul_inv_le_of_le_mul⟩ := mul_inv_le_iff
alias ⟨mul_le_of_le_mul_inv, le_mul_inv_of_mul_le⟩ := le_mul_inv_iff
alias ⟨le_of_one_le_mul_inv, one_le_mul_inv_of_le⟩ := one_le_mul_inv
alias ⟨le_of_mul_inv_le_one, mul_inv_le_one_of_le⟩ := mul_inv_le_one

end MulRightMono

end Units

namespace IsUnit

section MulLeftMono
variable [MulLeftMono M] {a b c : M} (ha : IsUnit a)

include ha

/--
@isnad1 id=mullecan.1h2v.s5.5231271368aa from=seed src=0 shape=85efe07c vocab=7f74c656
-/
theorem mulLECancellable : MulLECancellable a :=
  ha.unit.mulLECancellable_val

/--
@isnad1 id=iff.1h4v.s6.3c4f62e67ebf from=seed src=0 shape=608d011d vocab=cbc1ef55
-/
theorem mul_le_mul_left : a * b ≤ a * c ↔ b ≤ c :=
  ha.unit.mul_le_mul_iff_left

/--
@isnad1 id=le.2h4v.s6.7bd3335cd6a7 from=seed src=0 shape=c20715a5 vocab=cbc1ef55
-/
alias ⟨le_of_mul_le_mul_left, _⟩ := mul_le_mul_left

end MulLeftMono

section MulRightMono
variable [MulRightMono M] {a b c : M} (hc : IsUnit c)

include hc

/--
@isnad1 id=iff.1h4v.s6.ce7714ce2bc7 from=seed src=0 shape=80f64e77 vocab=de6a4ec6
-/
theorem mul_le_mul_right : a * c ≤ b * c ↔ a ≤ b :=
  hc.unit.mul_le_mul_iff_right

/--
@isnad1 id=le.2h4v.s6.4fba41e32b0e from=seed src=0 shape=8386e971 vocab=de6a4ec6
-/
alias ⟨le_of_mul_le_mul_right, _⟩ := mul_le_mul_right

end MulRightMono

end IsUnit
