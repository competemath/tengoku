import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_EisensteinSeries_WeierstrassZeta
import Tengoku.FltAnthropic.P2M.Sol.S_EisensteinSeries_weierstrassZeta_add_one_and_add_tau_and_smul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_EisensteinSeries_weierstrassZeta_add_one_and_add_tau_and_smul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped Real MatrixGroups

/--
@isnad1 id=and.0h1v.s11.d3716711af04 from=translated src=- shape=44f9ebee vocab=786a290c
-/
theorem EisensteinSeries.weierstrassZeta_add_one_and_add_tau_and_smul (τ : UpperHalfPlane) :
    (∀ z : ℂ, (∀ v : Fin 2 → ℤ, z ≠ (v 0 : ℂ) * τ + v 1) →
        EisensteinSeries.weierstrassZeta τ (z + 1) =
          EisensteinSeries.weierstrassZeta τ z + EisensteinSeries.G2 τ) ∧
    (∀ z : ℂ, (∀ v : Fin 2 → ℤ, z ≠ (v 0 : ℂ) * τ + v 1) →
        EisensteinSeries.weierstrassZeta τ (z + τ) =
          EisensteinSeries.weierstrassZeta τ z +
            ((τ : ℂ) * EisensteinSeries.G2 τ - 2 * π * Complex.I)) ∧
    (∀ (γ : SL(2, ℤ)) (z : ℂ),
        EisensteinSeries.weierstrassZeta (γ • τ) (z / UpperHalfPlane.denom γ τ) =
          UpperHalfPlane.denom γ τ * EisensteinSeries.weierstrassZeta τ z) := by exact @_root_.P2MW.S_EisensteinSeries_weierstrassZeta_add_one_and_add_tau_and_smul.solution τ
