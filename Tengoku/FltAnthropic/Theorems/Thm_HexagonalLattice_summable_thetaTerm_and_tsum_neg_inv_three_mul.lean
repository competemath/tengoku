import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_HexagonalLattice_summable_thetaTerm_and_tsum_neg_inv_three_mul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HexagonalLattice_summable_thetaTerm_and_tsum_neg_inv_three_mul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=and.1h1v.s9.eb10663e67f8 from=translated src=- shape=0f23317e vocab=3b5f28e8
-/
theorem HexagonalLattice.summable_thetaTerm_and_tsum_neg_inv_three_mul (σ : ℂ) (hσ : 0 < σ.im) :
    Summable (fun p : ℤ × ℤ =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * σ *
        ((p.1 : ℂ) ^ 2 + (p.1 : ℂ) * (p.2 : ℂ) + (p.2 : ℂ) ^ 2))) ∧
    (∑' p : ℤ × ℤ, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-1 / (3 * σ)) *
        ((p.1 : ℂ) ^ 2 + (p.1 : ℂ) * (p.2 : ℂ) + (p.2 : ℂ) ^ 2))) =
      -Complex.I * (Real.sqrt 3 : ℂ) * σ *
        ∑' p : ℤ × ℤ, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * σ *
          ((p.1 : ℂ) ^ 2 + (p.1 : ℂ) * (p.2 : ℂ) + (p.2 : ℂ) ^ 2)) := by exact @_root_.P2MW.S_HexagonalLattice_summable_thetaTerm_and_tsum_neg_inv_three_mul.solution σ hσ
