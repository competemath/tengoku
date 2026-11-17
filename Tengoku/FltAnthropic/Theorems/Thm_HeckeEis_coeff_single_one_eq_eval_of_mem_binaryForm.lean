import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep
import Tengoku.FltAnthropic.P2M.Sol.S_HeckeEis_coeff_single_one_eq_eval_of_mem_binaryForm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HeckeEis_coeff_single_one_eq_eval_of_mem_binaryForm.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped MatrixGroups

/--
@isnad1 id=eq.1h3v.s8.aced9140a8ed from=translated src=- shape=20d5237c vocab=fae6b8ac
-/
theorem HeckeEis.coeff_single_one_eq_eval_of_mem_binaryForm {K : Type*} [CommRing K] {n : ℕ}
    {P : MvPolynomial (Fin 2) K} (hP : P ∈ HeckeEis.BinaryForm K n) :
    MvPolynomial.coeff (Finsupp.single 1 n) P = MvPolynomial.eval ![0, 1] P := by exact @_root_.P2MW.S_HeckeEis_coeff_single_one_eq_eval_of_mem_binaryForm.solution K _ n P hP
