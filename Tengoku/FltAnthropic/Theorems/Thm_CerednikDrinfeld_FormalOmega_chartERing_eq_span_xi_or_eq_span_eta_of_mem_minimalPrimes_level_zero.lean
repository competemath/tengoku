import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Tengoku.FltAnthropic.P2M.Sol.S_CerednikDrinfeld_FormalOmega_chartERing_eq_span_xi_or_eq_span_eta_of_mem_minimalPrimes_level_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CerednikDrinfeld_FormalOmega_chartERing_eq_span_xi_or_eq_span_eta_of_mem_minimalPrimes_level_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.chartERing.eq_span_xi_or_eq_span_eta_of_mem_minimalPrimes_level_zero
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (r : ℕ) (hπ : (Ideal.span ({π} : Set 𝒪)).IsMaximal)
    (P : Ideal ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})))
    (hP : P ∈ minimalPrimes ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}))) :
    P = Ideal.span {Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r)} ∨ P = Ideal.span {Ideal.Quotient.mk _ (chartERing.η 𝒪 π r)} := by exact @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_chartERing_eq_span_xi_or_eq_span_eta_of_mem_minimalPrimes_level_zero.solution 𝒪 _ π r hπ P hP
