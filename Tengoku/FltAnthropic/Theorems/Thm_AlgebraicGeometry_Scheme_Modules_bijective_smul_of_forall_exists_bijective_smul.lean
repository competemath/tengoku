import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_bijective_smul_of_forall_exists_bijective_smul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_bijective_smul_of_forall_exists_bijective_smul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.bijective_smul_of_forall_exists_bijective_smul
    {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) (V : X.Opens)
    (h : ∀ x ∈ V, ∃ U : X.Opens, x ∈ U ∧ ∀ W : X.Opens, W ≤ U →
      Function.Bijective fun g : Γ(X, W) => g • (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op σ : Γ(M, W))) :
    Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op σ : Γ(M, V)) := by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_smul_of_forall_exists_bijective_smul.solution X M σ V h
