import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_EllipticCurve_FrobeniusTrace
import Tengoku.FltAnthropic.P2M.Sol.S_ValuationSubring_smul_eq_self_of_mem_inertiaSubgroupIn_of_pow_eq_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ValuationSubring_smul_eq_self_of_mem_inertiaSubgroupIn_of_pow_eq_one.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=eq.5h7v.s8.d96e8507a9a2 from=translated src=- shape=8c8a46d9 vocab=ed2c28f2
-/
theorem ValuationSubring.smul_eq_self_of_mem_inertiaSubgroupIn_of_pow_eq_one
    {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L) {q : ℕ} (hq : q.Prime)
    (hA : A.LiesOverPrime q) {σ : L ≃ₐ[K] L} (hσ : σ ∈ A.inertiaSubgroupIn K)
    {ζ : L} {m : ℕ} (hm : ¬ q ∣ m) (hζ : ζ ^ m = 1) : σ ζ = ζ := by exact @_root_.P2MW.S_ValuationSubring_smul_eq_self_of_mem_inertiaSubgroupIn_of_pow_eq_one.solution K L _ _ _ A q hq hA σ hσ ζ m hm hζ
