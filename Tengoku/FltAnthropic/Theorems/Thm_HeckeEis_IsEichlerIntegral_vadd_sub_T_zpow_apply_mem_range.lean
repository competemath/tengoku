import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_EichlerIntegral
import Tengoku.FltAnthropic.P2M.Sol.S_HeckeEis_IsEichlerIntegral_vadd_sub_T_zpow_apply_mem_range

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HeckeEis_IsEichlerIntegral_vadd_sub_T_zpow_apply_mem_range.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped Manifold MatrixGroups

theorem HeckeEis.IsEichlerIntegral.vadd_sub_T_zpow_apply_mem_range {n : ℕ} {h : ℤ} (hh : h ≠ 0)
    {g : UpperHalfPlane → ℂ} {G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)} (hG : HeckeEis.IsEichlerIntegral n g G)
    (hper : Function.Periodic (g ∘ UpperHalfPlane.ofComplex) ((h : ℝ) : ℂ))
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (hzero : UpperHalfPlane.IsZeroAtImInfty g) (τ : UpperHalfPlane) :
    G ((h : ℝ) +ᵥ τ) - HeckeEis.binaryFormRepSL ℂ n (ModularGroup.T ^ h) (G τ)
      ∈ LinearMap.range (HeckeEis.binaryFormRepSL ℂ n (ModularGroup.T ^ h) - 1) := by exact @_root_.P2MW.S_HeckeEis_IsEichlerIntegral_vadd_sub_T_zpow_apply_mem_range.solution n h hh g G hG hper hhol hzero τ
