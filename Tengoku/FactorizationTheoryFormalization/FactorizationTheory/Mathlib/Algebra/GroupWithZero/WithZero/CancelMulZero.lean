/-
Copyright (c) 2026 Arav Paladiya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arav Paladiya
-/
module

public import Tengoku.Seed.Algebra.GroupWithZero.WithZero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cancellation in `WithZero`

Adjoining zero to a left-, right-, or two-sided cancellative multiplication preserves the
corresponding cancellation property away from zero.
-/

public section

assert_not_exists DenselyOrdered Ring

namespace WithZero

variable {α : Type*}

/-- Adjoining zero preserves left cancellation.
@isnad1 id=isleftca.0h1v.s4.57c707146430 from=translated src=- shape=9499e9bc vocab=df6bb4bb
-/
instance instIsLeftCancelMulZero [Mul α] [IsLeftCancelMul α] :
    IsLeftCancelMulZero (WithZero α) where
  mul_left_cancel_of_ne_zero {a} ha b c h := by
    lift a to α using ha
    induction b using recZeroCoe with
    | zero =>
      induction c using recZeroCoe with
      | zero => rfl
      | coe c => simp at h
    | coe b =>
      induction c using recZeroCoe with
      | zero => simp at h
      | coe c =>
        have h' : a * b = a * c := coe_injective (by simpa only [coe_mul] using h)
        exact congrArg (fun x : α ↦ (x : WithZero α)) (mul_left_cancel h')

/-- Adjoining zero preserves right cancellation.
@isnad1 id=isrightc.0h1v.s4.acef2222f6d9 from=translated src=- shape=9499e9bc vocab=e0c54a96
-/
instance instIsRightCancelMulZero [Mul α] [IsRightCancelMul α] :
    IsRightCancelMulZero (WithZero α) where
  mul_right_cancel_of_ne_zero {a} ha b c h := by
    lift a to α using ha
    induction b using recZeroCoe with
    | zero =>
      induction c using recZeroCoe with
      | zero => rfl
      | coe c => simp at h
    | coe b =>
      induction c using recZeroCoe with
      | zero => simp at h
      | coe c =>
        have h' : b * a = c * a := coe_injective (by simpa only [coe_mul] using h)
        exact congrArg (fun x : α ↦ (x : WithZero α)) (mul_right_cancel h')

/-- Adjoining zero preserves two-sided cancellation.
@isnad1 id=iscancel.0h1v.s4.154914ff9cb3 from=translated src=- shape=9499e9bc vocab=b6f03975
-/
instance instIsCancelMulZero [Mul α] [IsCancelMul α] : IsCancelMulZero (WithZero α) where

end WithZero
