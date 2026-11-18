import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_UpperHalfPlane_finite_stabilizer_and_isCyclic_of_det_eq_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_UpperHalfPlane_finite_stabilizer_and_isCyclic_of_det_eq_one.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open Filter UpperHalfPlane
open scoped MatrixGroups Topology

theorem UpperHalfPlane.finite_stabilizer_and_isCyclic_of_det_eq_one
    (Γ : Subgroup (GL (Fin 2) ℝ))
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    [hdisc : DiscreteTopology ↥Γ] (τ : ℍ) :
    Finite ↥(MulAction.stabilizer ↥Γ τ) ∧ IsCyclic ↥(MulAction.stabilizer ↥Γ τ) := by exact @_root_.P2MW.S_UpperHalfPlane_finite_stabilizer_and_isCyclic_of_det_eq_one.solution Γ hdet hdisc τ
