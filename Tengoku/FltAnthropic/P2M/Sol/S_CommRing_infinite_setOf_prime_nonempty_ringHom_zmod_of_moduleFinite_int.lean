import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_FrobeniusDensity_PrimeSums
import Tengoku.FltAnthropic.Theorems.Thm_FrobeniusDensity_degOneSum_add_log_isBigO

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CommRing_infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CommRing_infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int

set_option autoImplicit false

open Filter Topology Asymptotics

namespace DegreeOnePrimes

section fracfield

variable (R : Type*) [CommRing R] [IsDomain R] [CharZero R] [Module.Finite ℤ R]

end fracfield

/--
@isnad1 id=tendsto.0h0v.s5.35f8fa789bb1 from=translated src=- shape=9eb8b840 vocab=d84520e3
-/
theorem tendsto_log_sub_one : Tendsto (fun s : ℝ => Real.log (s - 1)) (𝓝[>] (1 : ℝ)) atBot := by
  have h1 : Tendsto (fun s : ℝ => s - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun s : ℝ => s - 1) (𝓝 (1 : ℝ)) (𝓝 (1 - 1)) :=
        (continuous_sub_right (1 : ℝ)).tendsto 1
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact Set.mem_Ioi.mpr (sub_pos.mpr (Set.mem_Ioi.mp hs))
  exact Real.tendsto_log_nhdsGT_zero.comp h1

end DegreeOnePrimes
