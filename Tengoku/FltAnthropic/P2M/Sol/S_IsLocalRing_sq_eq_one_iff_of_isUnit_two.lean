import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsLocalRing_sq_eq_one_iff_of_isUnit_two.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open_scoped`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsLocalRing_sq_eq_one_iff_of_isUnit_two

set_option autoImplicit false

namespace IsLocalRing export _root_.IsLocalRing (isUnit_or_isUnit_of_isUnit_add) end IsLocalRing
open scoped _root_.IsLocalRing in

theorem IsLocalRing.mul_self_eq_one_iff_of_isUnit_two {R : Type} [CommRing R] [IsLocalRing R]
    (h2 : IsUnit (2 : R)) (u : R) : u * u = 1 ↔ u = 1 ∨ u = -1 := by
  constructor
  · intro hu
    have hfac : (u - 1) * (u + 1) = 0 := by
      have : (u - 1) * (u + 1) = u * u - 1 := by ring
      rw [this, hu, sub_self]
    have h2' : IsUnit ((u + 1) + (1 - u)) := by
      have : (u + 1) + (1 - u) = (2 : R) := by ring
      rwa [this]
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h2' with h | h
    · left
      have := (h.mul_left_eq_zero).mp hfac
      exact sub_eq_zero.mp this
    · right
      have hfac' : (u + 1) * (1 - u) = 0 := by
        have : (u + 1) * (1 - u) = -((u - 1) * (u + 1)) := by ring
        rw [this, hfac, neg_zero]
      have := (h.mul_left_eq_zero).mp hfac'
      exact eq_neg_of_add_eq_zero_left this
  · rintro (rfl | rfl) <;> ring

theorem solution {R : Type} [CommRing R] [IsLocalRing R]
    (h2 : IsUnit (2 : R)) (u : R) : u ^ 2 = 1 ↔ u = 1 ∨ u = -1 := by
  rw [sq, IsLocalRing.mul_self_eq_one_iff_of_isUnit_two h2]
