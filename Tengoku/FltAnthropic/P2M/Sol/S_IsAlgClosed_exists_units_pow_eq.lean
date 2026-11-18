import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GroupCohomology_Kummer

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsAlgClosed_exists_units_pow_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsAlgClosed_exists_units_pow_eq

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

theorem solution
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {n : ℕ} (hn : 0 < n) (x : Ωˣ) :
    ∃ y : Ωˣ, y ^ n = x := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (x : Ω) hn
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact x.ne_zero (by rw [← hz, zero_pow hn.ne'])
  exact ⟨Units.mk0 z hz0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hz])⟩
