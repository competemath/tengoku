import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Polynomial_natDegree_aeval_symm_minpoly_adjoin_coeff_le_of_transcendental

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Polynomial_natDegree_aeval_symm_minpoly_adjoin_coeff_le_of_transcendental.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=le.5h7v.s10.f9cef8ecb2c0 from=translated src=- shape=8f038efc vocab=3f6987f5
-/
theorem Polynomial.natDegree_aeval_symm_minpoly_adjoin_coeff_le_of_transcendental
    {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (x : F) (hxL : Transcendental L x) (hx0 : x ≠ 0)
    (f : F) (hint : IsIntegral (Algebra.adjoin L ({x} : Set F)) f) (m : ℕ)
    (h₂ : ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → x ∉ V →
      f * (x ^ m)⁻¹ ∈ V)
    (j : ℕ) (c : Polynomial L)
    (hc : Polynomial.aeval x c =
      (((minpoly (Algebra.adjoin L ({x} : Set F)) f).coeff j :
        Algebra.adjoin L ({x} : Set F)) : F)) :
    c.natDegree ≤ ((minpoly (Algebra.adjoin L ({x} : Set F)) f).natDegree - j) * m := by exact @_root_.P2MW.S_Polynomial_natDegree_aeval_symm_minpoly_adjoin_coeff_le_of_transcendental.solution L _ F _ _ x hxL hx0 f hint m h₂ j c hc
