import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Modularity
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_FreyPackage
import Tengoku.Seed.Algebra.Module.Torsion.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_FreyCurve_card_two_torsion_reductionMod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_FreyCurve_card_two_torsion_reductionMod.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
open WeierstrassCurve
namespace FreyCurve
/--
@isnad1 id=eq.2h2v.s8.a214a582f3b8 from=translated src=- shape=28ada59f vocab=539d7f8c
-/
theorem card_two_torsion_reductionMod (P : FreyPackage) {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    (hgood : (FreyPackage.freyCurveInt P).IsGoodPrimeFor q) :
    Nat.card (Submodule.torsionBy ℤ ((FreyPackage.freyCurveInt P).reductionMod q).toAffine.Point 2) = 4 := by exact @_root_.P2MW.S_FreyCurve_card_two_torsion_reductionMod.solution P q _ hq2 hgood
end FreyCurve
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
