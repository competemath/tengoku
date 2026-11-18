import Tengoku.Seed.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Tengoku.Seed.Topology.Algebra.InfiniteSum.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_jacobiTheta_two_eq_tprod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_jacobiTheta_two_eq_tprod.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
open scoped Real
open Complex
/--
@isnad1 id=eq.1h2v.s8.bc8c5022b52c from=translated src=- shape=cea6a5ea vocab=f123f2cf
-/
theorem _root_.Tengoku.FltAnthropic.jacobiTheta_two_eq_tprod (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiTheta₂ z τ = ∏' n : ℕ,
      ((1 - Complex.exp (2 * π * I * (n + 1) * τ)) *
        (1 + Complex.exp (π * I * (2 * n + 1) * τ + 2 * π * I * z)) *
        (1 + Complex.exp (π * I * (2 * n + 1) * τ - 2 * π * I * z))) := by exact @_root_.P2MW.S_jacobiTheta_two_eq_tprod.solution z τ hτ
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
