import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Ramification
import Tengoku.FltAnthropic.P2M.Sol.S_ValuationSubring_map_eq_zero_of_valuation_lt_one_of_charP

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ValuationSubring_map_eq_zero_of_valuation_lt_one_of_charP.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=eq.2h5v.s9.ea5fa0fa1ce0 from=translated src=- shape=06c74468 vocab=6b9f2380
-/
theorem ValuationSubring.map_eq_zero_of_valuation_lt_one_of_charP
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ) [Fact ℓ.Prime] (hA : A.LiesOverPrime ℓ)
    {k : Type*} [Field k] [CharP k ℓ] (red : ↥A →+* k)
    (τ : ↥A) (hτ : A.valuation (τ : AlgebraicClosure ℚ) < 1) :
    red τ = 0 := by exact @_root_.P2MW.S_ValuationSubring_map_eq_zero_of_valuation_lt_one_of_charP.solution A ℓ _ hA k _ _ red τ hτ
