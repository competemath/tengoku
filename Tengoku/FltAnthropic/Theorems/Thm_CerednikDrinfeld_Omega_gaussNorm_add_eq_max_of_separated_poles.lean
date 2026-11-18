import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_CerednikDrinfeld_Omega_gaussNorm_add_eq_max_of_separated_poles

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CerednikDrinfeld_Omega_gaussNorm_add_eq_max_of_separated_poles.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem CerednikDrinfeld.Omega.gaussNorm_add_eq_max_of_separated_poles
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (PA QA PB QB : Polynomial K) (hQA : QA ≠ 0) (hQB : QB ≠ 0) (hdeg : PA.degree < QA.degree)
    (h : ((∀ α ∈ QA.roots, Valued.v α < 1) ∧ ∀ β ∈ QB.roots, 1 ≤ Valued.v β) ∨
      ((∀ α ∈ QA.roots, Valued.v α ≤ 1) ∧ ∀ β ∈ QB.roots, 1 < Valued.v β)) :
    (PA * QB + PB * QA).support.sup (fun i => Valued.v ((PA * QB + PB * QA).coeff i)) =
      max ((PA * QB).support.sup fun i => Valued.v ((PA * QB).coeff i))
        ((PB * QA).support.sup fun i => Valued.v ((PB * QA).coeff i)) := by exact @_root_.P2MW.S_CerednikDrinfeld_Omega_gaussNorm_add_eq_max_of_separated_poles.solution K _ Γ₀ _ _ _ PA QA PB QB hQA hQB hdeg h
