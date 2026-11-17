import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep
import Tengoku.FltAnthropic.P2M.Sol.S_HeckeEis_exists_eq_smul_X_pow_of_binaryFormRepSL_lowerUnipotent_eq_self

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HeckeEis_exists_eq_smul_X_pow_of_binaryFormRepSL_lowerUnipotent_eq_self.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped MatrixGroups

/--
@isnad1 id=ex.4h5v.s12.8094864e1ab6 from=translated src=- shape=4e5afc0d vocab=0bb5f9ec
-/
theorem HeckeEis.exists_eq_smul_X_pow_of_binaryFormRepSL_lowerUnipotent_eq_self {R : Type*} [CommRing R] [IsDomain R] (n : ℕ)
    {h : ℤ} (hh : (h : R) ≠ 0) (hn : ∀ j : ℕ, 1 ≤ j → j ≤ n → (j : R) ≠ 0)
    (g : SL(2, ℤ)) (hg : (g : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; h, 1])
    (P : ↥(HeckeEis.BinaryForm R n)) (hP : HeckeEis.binaryFormRepSL R n g P = P) :
    ∃ c : R, (P : MvPolynomial (Fin 2) R) = c • MvPolynomial.X 1 ^ n := by exact @_root_.P2MW.S_HeckeEis_exists_eq_smul_X_pow_of_binaryFormRepSL_lowerUnipotent_eq_self.solution R _ _ n h hh hn g hg P hP
