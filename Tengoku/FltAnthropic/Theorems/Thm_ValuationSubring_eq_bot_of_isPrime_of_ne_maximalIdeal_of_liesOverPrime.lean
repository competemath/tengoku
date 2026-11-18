import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Ramification
import Tengoku.FltAnthropic.P2M.Sol.S_ValuationSubring_eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ValuationSubring_eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem ValuationSubring.eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime
    {p : ℕ} (hp : p.Prime) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (𝔮 : Ideal ↥A) [𝔮.IsPrime] (h𝔮 : 𝔮 ≠ IsLocalRing.maximalIdeal ↥A) : 𝔮 = ⊥ := by exact @_root_.P2MW.S_ValuationSubring_eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime.solution p hp A hA 𝔮 _ h𝔮
