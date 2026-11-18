import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_ModularGroup_exists_bounds_smul_of_mem_fd_of_im_le

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularGroup_exists_bounds_smul_of_mem_fd_of_im_le.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped UpperHalfPlane MatrixGroups

/--
@isnad1 id=ex.0h2v.s9.7822c9c6c055 from=translated src=- shape=dd24ac1c vocab=a4f5eea0
-/
theorem ModularGroup.exists_bounds_smul_of_mem_fd_of_im_le (S : Finset SL(2, ℤ)) (Y : ℝ) :
    ∃ B y₀ Y₁ : ℝ, 0 < y₀ ∧ ∀ σ ∈ S, ∀ z ∈ ModularGroup.fd, z.im ≤ Y →
      |(σ • z).re| ≤ B ∧ y₀ ≤ (σ • z).im ∧ (σ • z).im ≤ Y₁ := by exact @_root_.P2MW.S_ModularGroup_exists_bounds_smul_of_mem_fd_of_im_le.solution S Y
