import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsLocalRing_isUnit_natCast_guardPrime_sub_one_div_two_of_charP_two.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsLocalRing_isUnit_natCast_guardPrime_sub_one_div_two_of_charP_two

set_option autoImplicit false

theorem solution
    (R : Type*) [CommRing R] [IsLocalRing R] [CharP (IsLocalRing.ResidueField R) 2]
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) :
    IsUnit (((ℓg - 1) / 2 : ℕ) : R) := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast]
  intro h
  have hd := (CharP.cast_eq_zero_iff (IsLocalRing.ResidueField R) 2 _).mp h
  omega
