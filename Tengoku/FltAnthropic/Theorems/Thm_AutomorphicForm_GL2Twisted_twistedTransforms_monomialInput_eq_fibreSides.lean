import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_GL2TwistedMonomialFibres
import Tengoku.FltAnthropic.P2M.Sol.S_AutomorphicForm_GL2Twisted_twistedTransforms_monomialInput_eq_fibreSides

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AutomorphicForm_GL2Twisted_twistedTransforms_monomialInput_eq_fibreSides.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open AutomorphicForm.GL2Twisted

theorem
AutomorphicForm.GL2Twisted.twistedTransforms_monomialInput_eq_fibreSides
    (i l : ℕ) (c : ℝ → ℂ) (hc : Continuous c) (hcs : HasCompactSupport c) (a₁ a₂ r θ : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hr : 0 < r) (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi) :
    twistedSplitTransform (fun g : GL (Fin 2) ℂ => c (invFrobSq g) * ((monomialInput i l g : ℝ) : ℂ)) a₁ a₂ =
        splitFibreSide i l c a₁ a₂ ∧
    twistedEllipticTransform (fun g : GL (Fin 2) ℂ => c (invFrobSq g) * ((monomialInput i l g : ℝ) : ℂ)) r θ =
        ellipticFibreSide i l c r θ := by exact @_root_.P2MW.S_AutomorphicForm_GL2Twisted_twistedTransforms_monomialInput_eq_fibreSides.solution i l c hc hcs a₁ a₂ r θ ha₁ ha₂ hr hθ
