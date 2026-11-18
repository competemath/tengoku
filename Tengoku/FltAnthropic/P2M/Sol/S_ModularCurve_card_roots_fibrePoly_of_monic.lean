import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_FibrePoly

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_card_roots_fibrePoly_of_monic.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_card_roots_fibrePoly_of_monic

open Polynomial ModularCurve

/--
@isnad1 id=eq.1h3v.s5.54fc82d40f4f from=translated src=- shape=624d6bd2 vocab=00e2b483
-/
theorem solution {K : Type*} [Field K] [IsAlgClosed K]
    {Φ : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic) (a : K) :
    Multiset.card (fibrePoly Φ a).roots = Φ.natDegree := by
  rw [← (IsAlgClosed.splits (fibrePoly Φ a)).natDegree_eq_card_roots]
  exact hΦ.natDegree_map _
