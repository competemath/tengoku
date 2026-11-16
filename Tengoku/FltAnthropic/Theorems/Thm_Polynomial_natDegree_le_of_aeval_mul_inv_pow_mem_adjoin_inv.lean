import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Polynomial_natDegree_le_of_aeval_mul_inv_pow_mem_adjoin_inv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Polynomial_natDegree_le_of_aeval_mul_inv_pow_mem_adjoin_inv.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=le.3h5v.s8.6236e559082a from=translated src=- shape=ecfb9793 vocab=6142cb46
-/
theorem Polynomial.natDegree_le_of_aeval_mul_inv_pow_mem_adjoin_inv
    {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (x : F) (hxL : Transcendental L x) (hx0 : x ≠ 0)
    (c : Polynomial L) (n : ℕ)
    (h : Polynomial.aeval x c * (x ^ n)⁻¹ ∈ Algebra.adjoin L ({x⁻¹} : Set F)) :
    c.natDegree ≤ n := by exact @_root_.P2MW.S_Polynomial_natDegree_le_of_aeval_mul_inv_pow_mem_adjoin_inv.solution L _ F _ _ x hxL hx0 c n h
