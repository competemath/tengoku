import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MvPowerSeries_span_singleton_isPrime_of_sub_linear_mem_sq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvPowerSeries_span_singleton_isPrime_of_sub_linear_mem_sq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open MvPowerSeries

theorem MvPowerSeries.span_singleton_isPrime_of_sub_linear_mem_sq
    {κ : Type u} [Field κ] (a b : κ) (hab : a ≠ 0 ∨ b ≠ 0)
    (ℓ : MvPowerSeries (Fin 2) κ)
    (hℓ : ℓ - (C a * X 0 + C b * X 1) ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ 2) :
    (Ideal.span {ℓ}).IsPrime ∧
    ((X 0 : MvPowerSeries (Fin 2) κ) ∉ Ideal.span {ℓ} ∨ (X 1 : MvPowerSeries (Fin 2) κ) ∉ Ideal.span {ℓ}) ∧
    (∀ P : Ideal (MvPowerSeries (Fin 2) κ), P.IsPrime → ℓ ∈ P →
      ((X 0 : MvPowerSeries (Fin 2) κ) ∉ P ∨ (X 1 : MvPowerSeries (Fin 2) κ) ∉ P) → P = Ideal.span {ℓ}) ∧
    (∀ (a' b' : κ) (h' : MvPowerSeries (Fin 2) κ),
      h' ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ 2 →
      C a' * X 0 + C b' * X 1 + h' ∈ Ideal.span {ℓ} → a * b' - a' * b = 0) := by exact @_root_.P2MW.S_MvPowerSeries_span_singleton_isPrime_of_sub_linear_mem_sq.solution κ _ a b hab ℓ hℓ
