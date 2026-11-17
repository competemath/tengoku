import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ConstantTerm
import Tengoku.FltAnthropic.Definitions.Def_NumberField_StandardGlobalAddCharRat
import Tengoku.FltAnthropic.P2M.Sol.S_AutomorphicForm_LocalFunctionSpace_eq_zero_of_forall_mul_unipotent_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AutomorphicForm_LocalFunctionSpace_eq_zero_of_forall_mul_unipotent_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem AutomorphicForm.LocalFunctionSpace.eq_zero_of_forall_mul_unipotent_eq
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (W : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hpsi : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      W (AutomorphicForm.unipotentGL2 x * g) = NumberField.StandardAddChar.psiV p x * W g)
    (hsm : ∃ K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)),
      IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ K, (fun g => W (g * k)) = W)
    (hfix : ∀ x : p.adicCompletion ℚ, (fun g => W (g * AutomorphicForm.unipotentGL2 x)) = W) :
    W = 0 := by exact @_root_.P2MW.S_AutomorphicForm_LocalFunctionSpace_eq_zero_of_forall_mul_unipotent_eq.solution p W hpsi hsm hfix
