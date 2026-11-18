import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_UpperHalfPlane_two_dvd_natCard_stabilizer_of_neg_one_mem

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_UpperHalfPlane_two_dvd_natCard_stabilizer_of_neg_one_mem.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open Filter UpperHalfPlane
open scoped MatrixGroups Topology

/--
@isnad1 id=dvd.2h2v.s12.5901f6d3004f from=translated src=- shape=9914be11 vocab=2604e432
-/
theorem UpperHalfPlane.two_dvd_natCard_stabilizer_of_neg_one_mem
    (Γ : Subgroup (GL (Fin 2) ℝ))
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    (hneg : -1 ∈ Γ)
    [hdisc : DiscreteTopology ↥Γ] (τ : ℍ) :
    2 ∣ Nat.card ↥(MulAction.stabilizer ↥Γ τ) := by exact @_root_.P2MW.S_UpperHalfPlane_two_dvd_natCard_stabilizer_of_neg_one_mem.solution Γ hdet hneg hdisc τ
