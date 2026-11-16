import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_exists_isAffineOpen_le_inf_forall_mem_of_finset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_exists_isAffineOpen_le_inf_forall_mem_of_finset.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_isAffineOpen_le_inf_forall_mem_of_finset
    {X : Scheme.{u}} (W : X.Opens) (hW : IsAffineOpen W) (O : X.Opens) (F : Finset X)
    (hFW : ∀ x ∈ F, x ∈ W) (hFO : ∀ x ∈ F, x ∈ O) :
    ∃ W' : X.Opens, IsAffineOpen W' ∧ W' ≤ W ⊓ O ∧ ∀ x ∈ F, x ∈ W' := by exact @_root_.P2MW.S_AlgebraicGeometry_exists_isAffineOpen_le_inf_forall_mem_of_finset.solution X W hW O F hFW hFO
