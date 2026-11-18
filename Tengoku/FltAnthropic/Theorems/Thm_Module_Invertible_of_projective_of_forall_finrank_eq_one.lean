import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Module_Invertible_of_projective_of_forall_finrank_eq_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Module_Invertible_of_projective_of_forall_finrank_eq_one.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u v

theorem Module.Invertible.of_projective_of_forall_finrank_eq_one
    {A : Type u} [CommRing A] (P : Type v) [AddCommGroup P] [Module A P]
    [Module.Finite A P] [Module.Projective A P]
    (h : ∀ (K : Type u) [Field K] [Algebra A K], Module.finrank K (TensorProduct A K P) = 1) :
    Module.Invertible A P := by exact @_root_.P2MW.S_Module_Invertible_of_projective_of_forall_finrank_eq_one.solution A _ P _ _ _ _ h
