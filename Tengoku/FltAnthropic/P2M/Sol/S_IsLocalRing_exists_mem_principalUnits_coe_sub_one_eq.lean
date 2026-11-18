import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_LocalRing_PrincipalUnits

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsLocalRing_exists_mem_principalUnits_coe_sub_one_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsLocalRing_exists_mem_principalUnits_coe_sub_one_eq

set_option autoImplicit false
open IsLocalRing

open IsLocalRing in
theorem solution {R : Type*} [CommRing R] [IsLocalRing R]
    {k : ℕ} (hk : 1 ≤ k) {x : R} (hx : x ∈ maximalIdeal R ^ k) :
    ∃ u ∈ principalUnits R k, (u : R) - 1 = x := by
  have hx1 : x ∈ maximalIdeal R := Ideal.pow_le_self (by omega) hx
  have hunit : IsUnit (1 + x) := by
    have h := isUnit_one_sub_self_of_mem_nonunits (-x) ((maximalIdeal R).neg_mem hx1)
    rwa [sub_neg_eq_add] at h
  refine ⟨hunit.unit, ?_, ?_⟩
  · rw [mem_principalUnits_iff, IsUnit.unit_spec, add_sub_cancel_left]; exact hx
  · rw [IsUnit.unit_spec, add_sub_cancel_left]
