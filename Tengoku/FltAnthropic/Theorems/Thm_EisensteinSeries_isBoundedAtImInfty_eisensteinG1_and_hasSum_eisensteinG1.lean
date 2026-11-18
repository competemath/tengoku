import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_EisensteinSeries_WeierstrassZeta
import Tengoku.FltAnthropic.P2M.Sol.S_EisensteinSeries_isBoundedAtImInfty_eisensteinG1_and_hasSum_eisensteinG1

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_EisensteinSeries_isBoundedAtImInfty_eisensteinG1_and_hasSum_eisensteinG1.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped Real

theorem EisensteinSeries.isBoundedAtImInfty_eisensteinG1_and_hasSum_eisensteinG1 (N : ℕ) [NeZero N] :
    (∀ v : Fin 2 → ℤ, (¬ ∀ i, (N : ℤ) ∣ v i) →
        UpperHalfPlane.IsBoundedAtImInfty (EisensteinSeries.eisensteinG1 N v)) ∧
    (∀ (b : ℤ), ¬ (N : ℤ) ∣ b → ∀ τ : UpperHalfPlane,
        HasSum (fun n : ℕ => (if n = 0 then π / N * Complex.cot (π * b / N) else
            -(2 * π * Complex.I) / N * ∑ k ∈ n.divisors,
              (Complex.exp (2 * π * Complex.I * b * k / N) -
                Complex.exp (-(2 * π * Complex.I * b * k / N)))) *
            Complex.exp (2 * π * Complex.I * τ) ^ n)
          (EisensteinSeries.eisensteinG1 N ![0, b] τ)) := by exact @_root_.P2MW.S_EisensteinSeries_isBoundedAtImInfty_eisensteinG1_and_hasSum_eisensteinG1.solution N _
