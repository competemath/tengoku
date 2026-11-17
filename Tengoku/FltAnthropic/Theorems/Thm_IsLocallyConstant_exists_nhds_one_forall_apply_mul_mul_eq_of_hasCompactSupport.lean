import Tengoku.Seed.Topology.Algebra.Group.Basic
import Tengoku.Seed.Topology.LocallyConstant.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_IsLocallyConstant_exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsLocallyConstant_exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem IsLocallyConstant.exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Y : Type*} [Zero Y]
    {f : G → Y} (hf : IsLocallyConstant f) (hsupp : HasCompactSupport f) :
    ∃ V ∈ nhds (1 : G), ∀ u ∈ V, ∀ u' ∈ V, ∀ g : G, f (u * g * u') = f g := by exact @_root_.P2MW.S_IsLocallyConstant_exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport.solution G _ _ _ Y _ f hf hsupp
