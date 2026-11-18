import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsLocalRing_isUnit_natCast_or_isUnit_natCast_of_coprime.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsLocalRing_isUnit_natCast_or_isUnit_natCast_of_coprime

set_option autoImplicit false

theorem solution
    {R : Type*} [CommRing R] [IsLocalRing R] {m n : ℕ} (h : Nat.Coprime m n) :
    IsUnit (m : R) ∨ IsUnit (n : R) := by
  obtain ⟨u, v, huv⟩ := Nat.Coprime.cast (R := R) h
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (huv ▸ isUnit_one) with hu | hv
  · exact Or.inl (isUnit_of_mul_isUnit_right hu)
  · exact Or.inr (isUnit_of_mul_isUnit_right hv)
