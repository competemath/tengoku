import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_LocalRing_PrincipalUnits
import Tengoku.FltAnthropic.Theorems.Thm_IsLocalRing_principalUnits_one_eq_ker_map_residue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsLocalRing_index_principalUnits_one.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsLocalRing_index_principalUnits_one

set_option autoImplicit false
open IsLocalRing

open IsLocalRing in
theorem solution {R : Type*} [CommRing R] [IsLocalRing R] :
    (principalUnits R 1).index = Nat.card (ResidueField R)ˣ := by
  have hsurj : Function.Surjective (Units.map (residue R : R →* ResidueField R)) :=
    surjective_units_map_of_local_ringHom _ residue_surjective inferInstance
  rw [IsLocalRing.principalUnits_one_eq_ker_map_residue, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]
