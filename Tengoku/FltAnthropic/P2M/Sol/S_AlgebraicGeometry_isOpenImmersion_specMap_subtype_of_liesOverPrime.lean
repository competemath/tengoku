import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Ramification
import Tengoku.FltAnthropic.Theorems.Thm_ValuationSubring_isLocalization_away_natCast_of_liesOverPrime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_isOpenImmersion_specMap_subtype_of_liesOverPrime.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_isOpenImmersion_specMap_subtype_of_liesOverPrime

set_option autoImplicit false

open AlgebraicGeometry

theorem solution
    (O : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) (hp : p.Prime) (hO : O.LiesOverPrime p) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom O.subtype)) := by
  haveI := ValuationSubring.isLocalization_away_natCast_of_liesOverPrime O p hp hO
  exact IsOpenImmersion.of_isLocalization ((p : ℕ) : ↥O)
