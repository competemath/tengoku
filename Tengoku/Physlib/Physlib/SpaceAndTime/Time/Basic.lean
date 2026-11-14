/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Tengoku
/-!
# Time

`Time` represents instants with a fixed but arbitrary unit and orientation. It is an
affine space over `ℝ`: two instants determine a real-valued elapsed time, and adding
such a duration to an instant produces another instant. There is no distinguished zero.

The field `Time.val` is an implementation coordinate, not a frame-relative time
coordinate. A reference frame chooses its own time origin. Import
`Physlib.SpaceAndTime.Time.InnerProductSpace` to use the inner product space structure with the
implicit origin `Time.mk 0`, including addition of instants, norms, and derivatives.
-/

@[expose] public section
namespace Tengoku.Physlib end Tengoku.Physlib open Tengoku.Physlib 
/-!
# A. The `Time` type
-/

/-- An instant in time with a given unit and orientation, but no distinguished origin. -/
@[ext]
structure _root_.Tengoku.Physlib.Time where
  /-- The implementation coordinate associated with an instant. -/
  val : ℝ

namespace Tengoku.Physlib.Time

lemma val_injective : Function.Injective val := fun _ _ h => Time.ext h

instance : Nonempty Time := ⟨⟨0⟩⟩

/-!
# B. The affine structure
-/

instance : VAdd ℝ Time where
  vadd dt t := ⟨dt + t.val⟩

@[simp]
lemma vadd_val (dt : ℝ) (t : Time) : (dt +ᵥ t).val = dt + t.val := rfl

instance : VSub ℝ Time where
  vsub t₁ t₂ := t₁.val - t₂.val

@[simp]
lemma vsub_eq_val (t₁ t₂ : Time) : t₁ -ᵥ t₂ = t₁.val - t₂.val := rfl

instance : AddTorsor ℝ Time where
  zero_vadd t := by ext; simp
  add_vadd dt₁ dt₂ t := by ext; simp [add_assoc]
  vsub_vadd' t₁ t₂ := by ext; simp
  vadd_vsub' dt t := by simp

end Tengoku.Physlib.Time
-- Tengoku: root names of this library moved to Tengoku.Physlib so they do not collide with other libraries (generated)
