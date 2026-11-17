import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Modularity
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_FreyPackage
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Tengoku.FltAnthropic.P2M.Sol.S_FreyCurve_eight_mul_Psi2Sq_eval_reductionMod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_FreyCurve_eight_mul_Psi2Sq_eval_reductionMod.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
namespace FreyCurve
open WeierstrassCurve
theorem eight_mul_Psi2Sq_eval_reductionMod (P : FreyPackage) {q : ℕ} [Fact q.Prime]
    (x : ZMod q) :
    8 * (((FreyPackage.freyCurveInt P).reductionMod q).Ψ₂Sq.eval x) =
      2 * x * (4 * x - ((P.a : ZMod q)) ^ P.p) * (4 * x + ((P.b : ZMod q)) ^ P.p) := by exact @_root_.P2MW.S_FreyCurve_eight_mul_Psi2Sq_eval_reductionMod.solution P q _ x
end FreyCurve
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
