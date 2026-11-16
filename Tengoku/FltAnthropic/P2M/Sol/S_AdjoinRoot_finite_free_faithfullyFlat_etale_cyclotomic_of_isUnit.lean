import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AdjoinRoot_finite_free_faithfullyFlat_etale_cyclotomic_of_isUnit.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AdjoinRoot_finite_free_faithfullyFlat_etale_cyclotomic_of_isUnit

set_option autoImplicit false

open Polynomial

universe u

namespace CycEtale29

variable {R : Type u} [CommRing R]

theorem separable_cyclotomic (m : ℕ) (hm : IsUnit ((m : ℕ) : R)) : (cyclotomic m R).Separable := by
  have h1 : (X ^ m - C ((1 : Rˣ) : R)).Separable := separable_X_pow_sub_C_unit 1 hm
  rw [Units.val_one, C_1] at h1
  exact h1.of_dvd (cyclotomic.dvd_X_pow_sub_one m R)

end CycEtale29
