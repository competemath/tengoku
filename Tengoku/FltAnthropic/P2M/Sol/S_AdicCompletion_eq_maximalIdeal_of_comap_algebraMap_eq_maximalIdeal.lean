import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AdicCompletionLocalRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AdicCompletion_eq_maximalIdeal_of_comap_algebraMap_eq_maximalIdeal.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AdicCompletion_eq_maximalIdeal_of_comap_algebraMap_eq_maximalIdeal

set_option autoImplicit false

open IsLocalRing

theorem solution
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (P : Ideal (AdicCompletion (maximalIdeal R) R)) [P.IsPrime]
    (hP : Ideal.comap (algebraMap R (AdicCompletion (maximalIdeal R) R)) P = maximalIdeal R) :
    P = maximalIdeal (AdicCompletion (maximalIdeal R) R) := by
  have hle : maximalIdeal (AdicCompletion (maximalIdeal R) R) ≤ P := by
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_le_iff_le_comap, hP]
  exact ((IsLocalRing.maximalIdeal.isMaximal _).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm
