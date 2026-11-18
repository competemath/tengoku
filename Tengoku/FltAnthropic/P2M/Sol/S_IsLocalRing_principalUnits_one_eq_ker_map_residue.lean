import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_LocalRing_PrincipalUnits

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsLocalRing_principalUnits_one_eq_ker_map_residue.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsLocalRing_principalUnits_one_eq_ker_map_residue

set_option autoImplicit false
open IsLocalRing

open IsLocalRing in
theorem solution {R : Type*} [CommRing R] [IsLocalRing R] :
    principalUnits R 1 = (Units.map (residue R : R →* ResidueField R)).ker := by
  ext u
  rw [mem_principalUnits_iff, pow_one, MonoidHom.mem_ker, Units.ext_iff, Units.coe_map, Units.val_one,
    MonoidHom.coe_coe, ← residue_eq_zero_iff, map_sub, map_one, sub_eq_zero]
