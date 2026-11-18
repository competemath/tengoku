import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_FibrePoly

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_monic_fibrePoly.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_monic_fibrePoly

open Polynomial ModularCurve

/--
@isnad1 id=monic.1h3v.s5.e695ec9bac14 from=translated src=- shape=c1b1a2fc vocab=781086ff
-/
theorem solution {K : Type*} [Field K] {Φ : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic)
    (a : K) : (fibrePoly Φ a).Monic := by
  exact hΦ.map _
