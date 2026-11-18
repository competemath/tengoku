import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsLocalRing_charP_residueField_of_natCast_mem_maximalIdeal.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsLocalRing_charP_residueField_of_natCast_mem_maximalIdeal

set_option autoImplicit false

/--
@isnad1 id=charp.1h2v.s6.d968ce1bd5bb from=translated src=- shape=4f170ddd vocab=65746e26
-/
theorem solution
    (A : Type*) [CommRing A] [IsLocalRing A] (p : ℕ) [Fact p.Prime]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) :
    CharP (IsLocalRing.ResidueField A) p := by
  have h0 : ((p : ℕ) : IsLocalRing.ResidueField A) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff]
    exact hAp
  exact (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 h0
