import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_EichlerIntegral
import Tengoku.FltAnthropic.P2M.Sol.S_HeckeEis_jFactor_pow_mul_eval_binaryFormRepSL

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HeckeEis_jFactor_pow_mul_eval_binaryFormRepSL.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped Manifold MatrixGroups ModularForm

theorem HeckeEis.jFactor_pow_mul_eval_binaryFormRepSL (n : ℕ) (g : SL(2, ℤ)) (τ : UpperHalfPlane)
    (P : ↥(HeckeEis.BinaryForm ℂ n)) :
    HeckeEis.jFactor g τ ^ n * MvPolynomial.eval ![(1 : ℂ), -(((g • τ : UpperHalfPlane)) : ℂ)]
        ((HeckeEis.binaryFormRepSL ℂ n g P : ↥(HeckeEis.BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)
      = MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)] (P : MvPolynomial (Fin 2) ℂ) := by exact @_root_.P2MW.S_HeckeEis_jFactor_pow_mul_eval_binaryFormRepSL.solution n g τ P
