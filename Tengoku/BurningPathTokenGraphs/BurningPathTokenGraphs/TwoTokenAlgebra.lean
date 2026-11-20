import Tengoku.Seed.Algebra.Group.Int.Even
import Tengoku.Seed.Data.Int.ModEq
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Algebra for the two-token coordinate change

This file contains the exact absolute-value and parity identities used by the square model for
two-token path configurations.
-/

namespace BurningPath

/--
The linear change of coordinates `(p, q) ↦ (p + q, q - p)` sends the `ℓ₁` norm on
`ℤ × ℤ` to the `ℓ∞` norm.-/
theorem max_abs_add_sub (p q : ℤ) :
    max |p + q| |q - p| = |p| + |q| := by
  rcases le_total 0 p with hp | hp
  · rcases le_total 0 q with hq | hq
    · rw [abs_of_nonneg hp, abs_of_nonneg hq, abs_of_nonneg (add_nonneg hp hq),
        max_eq_left_iff, abs_le]
      omega
    · have hqp : q - p ≤ 0 := by omega
      rw [abs_of_nonneg hp, abs_of_nonpos hq, abs_of_nonpos hqp]
      calc
        max |p + q| (-(q - p)) = -(q - p) := max_eq_right (by rw [abs_le]; omega)
        _ = p + -q := by omega
  · rcases le_total 0 q with hq | hq
    · have hqp : 0 ≤ q - p := by omega
      rw [abs_of_nonpos hp, abs_of_nonneg hq, abs_of_nonneg hqp]
      calc
        max |p + q| (q - p) = q - p := max_eq_right (by rw [abs_le]; omega)
        _ = -p + q := by omega
    · rw [abs_of_nonpos hp, abs_of_nonpos hq, abs_of_nonpos (add_nonpos hp hq)]
      calc
        max (-(p + q)) |q - p| = -(p + q) := max_eq_left (by rw [abs_le]; omega)
        _ = -p + -q := by omega

/-- The natural-valued form of `max_abs_add_sub`, suited to graph distances.-/
theorem max_natAbs_add_sub (p q : ℤ) :
    max (p + q).natAbs (q - p).natAbs = p.natAbs + q.natAbs := by
  apply Int.ofNat_inj.mp
  simpa only [Nat.cast_max, Int.natCast_natAbs, Nat.cast_add] using max_abs_add_sub p q

/--
The two transformed coordinate differences have maximum absolute value equal to the original
`ℓ₁` coordinate distance.-/
theorem max_natAbs_sumDiff_sub_sumDiff (x y x' y' : ℤ) :
    max ((x + y) - (x' + y')).natAbs ((y - x) - (y' - x')).natAbs =
      (x - x').natAbs + (y - y').natAbs := by
  rw [show (x + y) - (x' + y') = (x - x') + (y - y') by omega]
  rw [show (y - x) - (y' - x') = (y - y') - (x - x') by omega]
  exact max_natAbs_add_sub (x - x') (y - y')

/-- Translating both points by the same vector leaves the transformed-coordinate distance fixed.-/
theorem max_natAbs_sumDiff_translation (x y x' y' a b : ℤ) :
    max (((x + a) + (y + b)) - ((x' + a) + (y' + b))).natAbs
        (((y + b) - (x + a)) - ((y' + b) - (x' + a))).natAbs =
      max ((x + y) - (x' + y')).natAbs ((y - x) - (y' - x')).natAbs := by
  apply congrArg₂ max
  · apply congrArg Int.natAbs
    omega
  · apply congrArg Int.natAbs
    omega

/-- The sum and difference coordinates of two integers are congruent modulo two.-/
theorem add_modEq_sub_two (x y : ℤ) :
    x + y ≡ y - x [ZMOD 2] := by
  rw [Int.modEq_iff_dvd]
  exact ⟨-x, by omega⟩

/-- Testing either transformed coordinate against a parity class gives the same result.-/
theorem add_modEq_iff_sub_modEq_two (x y σ : ℤ) :
    x + y ≡ σ [ZMOD 2] ↔ y - x ≡ σ [ZMOD 2] := by
  constructor
  · exact fun h ↦ (add_modEq_sub_two x y).symm.trans h
  · exact fun h ↦ (add_modEq_sub_two x y).trans h

/-- In particular, the sum and difference coordinates are either both even or both odd.-/
theorem even_add_iff_even_sub (x y : ℤ) :
    Even (x + y) ↔ Even (y - x) := by
  simp only [Int.even_add, Int.even_sub, iff_comm]

end BurningPath
