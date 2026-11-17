import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_EichlerIntegral
import Tengoku.FltAnthropic.P2M.Sol.S_HeckeEis_exists_pairing_binaryForm_linePow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HeckeEis_exists_pairing_binaryForm_linePow.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped MatrixGroups

/--
@isnad1 id=ex.0h1v.s15.dfeed910b395 from=translated src=- shape=c5d415a5 vocab=4c0f6fc2
-/
theorem HeckeEis.exists_pairing_binaryForm_linePow (n : ℕ) :
    ∃ B : ↥(HeckeEis.BinaryForm ℂ n) →ₗ[ℂ] ↥(HeckeEis.BinaryForm ℂ n) →ₗ[ℂ] ℂ,
      (∀ (g : SL(2, ℤ)) (P Q : ↥(HeckeEis.BinaryForm ℂ n)),
          B (HeckeEis.binaryFormRepSL ℂ n g P) (HeckeEis.binaryFormRepSL ℂ n g Q) = B P Q) ∧
      (∀ P Q : ↥(HeckeEis.BinaryForm ℂ n), B Q P = (-1) ^ n * B P Q) ∧
      (∀ P : ↥(HeckeEis.BinaryForm ℂ n), (∀ Q : ↥(HeckeEis.BinaryForm ℂ n), B P Q = 0) → P = 0) ∧
      (∀ τ σ : ℂ, B (HeckeEis.linePow n τ) (HeckeEis.linePow n σ) = (τ - σ) ^ n) := by exact @_root_.P2MW.S_HeckeEis_exists_pairing_binaryForm_linePow.solution n
