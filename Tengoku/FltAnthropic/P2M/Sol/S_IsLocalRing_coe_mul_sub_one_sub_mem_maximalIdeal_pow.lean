import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_LocalRing_PrincipalUnits

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsLocalRing_coe_mul_sub_one_sub_mem_maximalIdeal_pow.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsLocalRing_coe_mul_sub_one_sub_mem_maximalIdeal_pow

set_option autoImplicit false
open IsLocalRing

open IsLocalRing in
/--
@isnad1 id=mem.2h4v.s8.a410358d34a4 from=translated src=- shape=3642be9a vocab=3c51f84f
-/
theorem solution {R : Type*} [CommRing R] [IsLocalRing R]
    {k : ℕ} {u v : Rˣ} (hu : u ∈ principalUnits R k) (hv : v ∈ principalUnits R k) :
    ((u * v : Rˣ) : R) - 1 - (((u : R) - 1) + ((v : R) - 1)) ∈ maximalIdeal R ^ (2 * k) := by
  have h : ((u * v : Rˣ) : R) - 1 - (((u : R) - 1) + ((v : R) - 1)) = ((u : R) - 1) * ((v : R) - 1) := by
    push_cast; ring
  rw [h, two_mul, pow_add]
  exact Ideal.mul_mem_mul hu hv
