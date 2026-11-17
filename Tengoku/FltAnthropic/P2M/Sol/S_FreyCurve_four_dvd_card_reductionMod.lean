import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Modularity
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_FreyPackage
import Tengoku.Seed.Algebra.Module.Torsion.Basic
import Tengoku.FltAnthropic.Theorems.Thm_FreyCurve_card_two_torsion_reductionMod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_FreyCurve_four_dvd_card_reductionMod.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_FreyCurve_four_dvd_card_reductionMod

open WeierstrassCurve Tengoku.FltAnthropic.FreyPackage

theorem solution (P : FreyPackage) {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    (hgood : (FreyPackage.freyCurveInt P).IsGoodPrimeFor q) :
    4 ∣ ((FreyPackage.freyCurveInt P).reductionMod q).card := by
  rw [← FreyCurve.card_two_torsion_reductionMod P hq2 hgood]
  exact AddSubgroup.card_dvd_of_injective
    (Submodule.torsionBy ℤ ((freyCurveInt P).reductionMod q).toAffine.Point 2).subtype.toAddMonoidHom
    (fun a b hab => Subtype.ext hab)
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
