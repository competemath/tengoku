import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep
import Tengoku.FltAnthropic.P2M.Sol.S_HeckeEis_exists_binaryForm_eq_mul_of_forall_eval_eq_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HeckeEis_exists_binaryForm_eq_mul_of_forall_eval_eq_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MvPolynomial in

theorem HeckeEis.exists_binaryForm_eq_mul_of_forall_eval_eq_zero (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [CharP K p] (n : ℕ) (F : MvPolynomial (Fin 2) K)
    (hF : F ∈ HeckeEis.BinaryForm K n)
    (hvan : ∀ v : Fin 2 → ZMod p,
      MvPolynomial.eval (fun i => ZMod.castHom (dvd_refl p) K (v i)) F = 0) :
    ∃ H : MvPolynomial (Fin 2) K, H ∈ HeckeEis.BinaryForm K (n - (p + 1)) ∧
      F = (X 0 ^ p * X 1 - X 0 * X 1 ^ p) * H := by exact @_root_.P2MW.S_HeckeEis_exists_binaryForm_eq_mul_of_forall_eval_eq_zero.solution p _ K _ _ n F hF hvan
