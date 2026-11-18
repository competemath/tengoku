import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_LocalRing_PrincipalUnits
import Tengoku.FltAnthropic.Theorems.Thm_IsLocalRing_pow_mem_principalUnits
import Tengoku.FltAnthropic.Theorems.Thm_IsDiscreteValuationRing_exists_mem_principalUnits_pow_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsDiscreteValuationRing_map_powMonoidHom_principalUnits.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsDiscreteValuationRing_map_powMonoidHom_principalUnits

set_option autoImplicit false
open IsLocalRing

open IsLocalRing in
theorem solution {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {p : ℕ} (hp : p.Prime) {e : ℕ} (hpe : Ideal.span {(p : R)} = IsLocalRing.maximalIdeal R ^ e)
    {k : ℕ} (hk : e < k) :
    (principalUnits R k).map (powMonoidHom p) = principalUnits R (k + e) := by
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    have hpe' : (p : R) ∈ IsLocalRing.maximalIdeal R ^ e := by
      rw [← hpe]; exact Ideal.mem_span_singleton_self _
    have h := IsLocalRing.pow_mem_principalUnits hp hpe' hu
    have hmin : k + e ≤ min (p * k) (k + e) := by
      refine le_min ?_ le_rfl
      calc k + e ≤ k + k := by omega
        _ = 2 * k := (two_mul k).symm
        _ ≤ p * k := Nat.mul_le_mul_right k hp.two_le
    exact principalUnits_antitone hmin h
  · intro w hw
    obtain ⟨u, hu, huw⟩ := IsDiscreteValuationRing.exists_mem_principalUnits_pow_eq hp.pos hpe hk hw
    exact ⟨u, hu, huw⟩
