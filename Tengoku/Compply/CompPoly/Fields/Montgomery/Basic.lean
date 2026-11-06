/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin, Georgios Raikos
-/
module

public import Tengoku.Seed.Data.Nat.ModEq
public import Tengoku.Seed.Data.ZMod.Basic
public import Tengoku.Seed.Algebra.Field.ZMod
public import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Montgomery Reduction

Radix-generic specification and correctness lemmas for single-word Montgomery reduction.
Word-specific implementations refine these results in sibling modules.
-/

@[expose] public section

namespace Montgomery

/-- The Montgomery divisibility identity: if `(negInv * p) % R = R - 1` (i.e.
`negInv = -p⁻¹ mod R`), then `R ∣ x + ((x mod R)·negInv mod R)·p` for every `x`.-/
theorem dvd_add (R p negInv : ℕ) (hR : 0 < R)
    (hnegInv : negInv * p % R = R - 1) (x : ℕ) :
    R ∣ x + ((x % R * negInv) % R) * p := by
  rw [Nat.dvd_iff_mod_eq_zero]
  rw [Nat.add_mod, Nat.mod_mul_mod (x % R * negInv) p R, Nat.mul_assoc]
  rw [← Nat.mul_mod_mod, hnegInv, Nat.add_mod_mod, add_comm, ← Nat.mul_add_one]
  rw [show R - 1 + 1 = R by omega, Nat.mul_mod_left]

end Montgomery
