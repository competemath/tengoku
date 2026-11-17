import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_EllipticCurve_FrobeniusTrace
import Tengoku.FltAnthropic.P2M.Sol.S_ValuationSubring_smul_eq_pow_of_isFrobeniusAt_of_pow_eq_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ValuationSubring_smul_eq_pow_of_isFrobeniusAt_of_pow_eq_one.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=eq.5h7v.s7.95a341d05387 from=translated src=- shape=e1184f08 vocab=61eb1754
-/
theorem ValuationSubring.smul_eq_pow_of_isFrobeniusAt_of_pow_eq_one
    {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L) {q : ℕ} (hq : q.Prime)
    (hA : A.LiesOverPrime q) {σ : L ≃ₐ[K] L} (hσ : A.IsFrobeniusAt σ q)
    {ζ : L} {m : ℕ} (hm : ¬ q ∣ m) (hζ : ζ ^ m = 1) : σ ζ = ζ ^ q := by exact @_root_.P2MW.S_ValuationSubring_smul_eq_pow_of_isFrobeniusAt_of_pow_eq_one.solution K L _ _ _ A q hq hA σ hσ ζ m hm hζ
